#!/usr/bin/env python3
"""Plot the README's recorded formalization progress from Git history."""

import argparse
import re
import subprocess
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D


ROOT = Path(__file__).resolve().parents[1]
PROGRESS = re.compile(r"\b\d{1,3}(?:\.\d+)?%\**\s+\((\d+)/(\d+) (?:milestones|modules|tests)\)")
STATUS_STYLES = {
    "🔴": ("Started", "#b32635", "o"),
    "🟠": ("In progress", "#b54b0b", "o"),
    "🟢": ("Almost done", "#15754d", "o"),
    "🏁": ("Complete", "#2857a5", "D"),
}
INK = "#192c27"
MUTED = "#516760"
PAPER = "#fcfdfb"


def git(*args):
    return subprocess.run(["git", *args], cwd=ROOT, check=True, capture_output=True, text=True).stdout


def score(label, status):
    match = PROGRESS.search(status)
    if match is None:
        return None
    completed, total = match.groups()
    symbol = status.strip()[0]
    if symbol not in STATUS_STYLES:
        raise ValueError(f"Unrecognized progress status for {label}: {status.strip()}")
    return 100 * int(completed) / int(total), f"{completed}/{total}", symbol


def progress(readme):
    section = readme.partition("\n## Verification progress\n")[2].split("\n## ", 1)[0]
    rows = {}
    for line in section.splitlines():
        columns = line.split("|")
        if columns[0] or len(columns) < 3:
            continue
        _, label, status, *_ = columns
        point = score(label, status)
        if point is not None:
            label = label.strip().replace(r"\*", "*")
            if label == "C shell assurance":
                label = "Shell assurance"
            rows[label] = point
    return rows


def milestone_credits(readme):
    section = readme.partition("\n#### Milestone credits by commit\n")[2].split("\n##", 1)[0]
    credits = {}
    for line in section.splitlines():
        columns = line.split("|")
        if columns[0] or len(columns) < 5:
            continue
        _, revision, label, status, *_ = columns
        point = score(label, status)
        if point is not None:
            credits.setdefault(revision.strip().strip("`"), {})[label.strip()] = point
    return credits


def history(*, committed_only=False):
    current_readme = git("show", "HEAD:README.md") if committed_only else (ROOT / "README.md").read_text(encoding="utf-8")
    credits = milestone_credits(current_readme)
    carried = {}
    snapshots = []
    for commit in git("rev-list", "--reverse", "--first-parent", "HEAD").splitlines():
        changed = git("diff-tree", "--root", "--no-commit-id", "--name-only", "-r", commit).splitlines()
        if changed == ["docs/progress.png"]:
            continue
        if "README.md" in git("ls-tree", "--name-only", commit, "--", "README.md").splitlines():
            rows = progress(git("show", f"{commit}:README.md"))
        else:
            rows = {}
        revision = commit[:7]
        for label, point in credits.get(revision, {}).items():
            carried[label] = rows[label], point
        # Carry a credit until the committed table records a different score for that area.
        for label, (previous, credited) in list(carried.items()):
            if rows.get(label) == previous:
                rows[label] = credited
            else:
                del carried[label]
        snapshots.append((revision, rows))

    first_recorded = next((i for i, (_, rows) in enumerate(snapshots) if rows), len(snapshots))
    snapshots = snapshots[first_recorded:]
    if not committed_only:
        working_tree = progress(current_readme)
        if not snapshots or working_tree != snapshots[-1][1]:
            snapshots.append(("Working tree", working_tree))
    return snapshots


def draw(snapshots, output):
    if not snapshots or not snapshots[-1][1]:
        raise SystemExit("No formalization progress rows in README.md")
    latest = snapshots[-1][1]
    baseline = dict.fromkeys(latest, (0, "", "🔴"))
    revisions, rows = zip(("0% baseline", baseline), *snapshots)

    figure, axis = plt.subplots(figsize=(11.3, 5.9), facecolor=PAPER)
    figure.subplots_adjust(left=0.085, right=0.680, bottom=0.20, top=0.73)
    figure.text(0.04, 0.92, "Formalization progress", fontsize=25, weight="bold", color=INK)
    commit_count = len(snapshots) - (snapshots[-1][0] == "Working tree")
    figure.text(0.04, 0.86, f"Recorded milestone percentages across {commit_count} mainline commits",
                fontsize=12, color=MUTED)
    handles = [
        Line2D([], [], color=color, marker=marker, linestyle="none", label=name)
        for name, color, marker in STATUS_STYLES.values()
    ]
    figure.legend(handles=handles, loc="upper left", bbox_to_anchor=(0.035, 0.835),
                  frameon=False, ncols=4, fontsize=10, labelcolor=INK)

    axis.set_facecolor(PAPER)
    axis.set_ylim(-7, 107)
    axis.axhspan(0, 100, color="#f0f3f5", zorder=0)
    axis.axhline(100, color="#9ba7ad", linestyle=(0, (3, 3)), linewidth=0.9)
    for percent in (0, 25, 50, 75):
        axis.axhline(percent, color="#dde3e7", linewidth=0.8)

    for label in latest:
        for i, (revision, snapshot) in enumerate(zip(revisions, rows)):
            point = snapshot.get(label)
            if point is None:
                continue
            percent, _, status = point
            _, color, marker = STATUS_STYLES[status]
            pending = revision == "Working tree"
            previous = rows[i - 1].get(label) if i else None
            if previous is not None:
                previous_percent, _, previous_status = previous
                style = "--" if pending else "-"
                axis.plot([i - 1, i], [previous_percent, previous_percent], linestyle=style,
                          color=STATUS_STYLES[previous_status][1], linewidth=1.8)
                axis.plot([i, i], [previous_percent, percent], linestyle=style, color=color, linewidth=1.8)
            axis.scatter(i, percent, s=25 if point != previous or pending else 14, marker=marker,
                         facecolors=PAPER if pending else color, edgecolors=color, zorder=3)

    last = len(revisions) - 1
    ordered = sorted(latest.items(), key=lambda item: item[1][0], reverse=True)
    label_y = 107
    for i, (label, (percent, fraction, status)) in enumerate(ordered):
        # Keep labels readable when several traces end at the same percentage.
        minimum = 7 * (len(ordered) - i - 1)
        label_y = max(minimum, min(percent, label_y - 7))
        _, color, _ = STATUS_STYLES[status]
        display_percent = f"{percent:.1f}".removesuffix(".0")
        axis.annotate(
            f"{label} · {display_percent}% ({fraction})", xy=(last, percent), xytext=(1.05, label_y),
            textcoords=axis.get_yaxis_transform(), va="center", color=color, fontsize=10,
            arrowprops={"arrowstyle": "-", "color": color, "linewidth": 1, "alpha": 0.65, "relpos": (0, 0.5)},
        )

    axis.set_xlim(-0.15, len(revisions) - 0.85)
    levels = [0, 25, 50, 75, 100]
    axis.set_yticks(levels, labels=[f"{level}%" for level in levels])
    axis.set_xticks(range(len(revisions)), labels=revisions, rotation=55, ha="right",
                    rotation_mode="anchor")
    axis.tick_params(axis="both", length=0, labelsize=9, colors=MUTED, pad=7)
    axis.spines[:].set_visible(False)
    axis.set_xlabel("Git history · oldest to newest", color=MUTED, fontsize=10, labelpad=12)
    figure.savefig(output, dpi=150, metadata={"Software": "tools/plot_progress.py"})
    plt.close(figure)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--committed-only", action="store_true", help="exclude working-tree README values")
    args = parser.parse_args()
    draw(history(committed_only=args.committed_only), ROOT / "docs/progress.png")
