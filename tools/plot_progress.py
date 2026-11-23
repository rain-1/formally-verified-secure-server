#!/usr/bin/env python3
"""Plot the README's recorded formalization progress from Git history."""

import math
import re
import subprocess
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt


ROOT = Path(__file__).resolve().parents[1]
PROGRESS = re.compile(r"\b(\d{1,3})%\**\s+\((\d+/\d+) (?:milestones|modules|tests)\)")
GREEN = "#15754d"
INK = "#192c27"
MUTED = "#516760"
PAPER = "#fcfdfb"


def git(*args):
    return subprocess.run(["git", *args], cwd=ROOT, check=True, capture_output=True, text=True).stdout


def progress(readme):
    section = readme.partition("\n## Verification progress\n")[2].split("\n## ", 1)[0]
    rows = {}
    for line in section.splitlines():
        columns = line.split("|")
        if columns[0] or len(columns) < 3:
            continue
        _, label, status, *_ = columns
        match = PROGRESS.search(status)
        if match:
            label = label.strip().replace(r"\*", "*")
            if label == "C shell assurance":
                label = "Shell assurance"
            percentage, fraction = match.groups()
            rows[label] = (int(percentage), fraction)
    return rows


def history():
    snapshots = []
    for commit in git("rev-list", "--reverse", "--first-parent", "HEAD").splitlines():
        if "README.md" in git("ls-tree", "--name-only", commit, "--", "README.md").splitlines():
            rows = progress(git("show", f"{commit}:README.md"))
        else:
            rows = {}
        snapshots.append((commit[:7], rows))

    first = next((i for i, (_, rows) in enumerate(snapshots) if rows), len(snapshots))
    snapshots = snapshots[first:]
    working_tree = progress((ROOT / "README.md").read_text(encoding="utf-8"))
    if not snapshots or working_tree != snapshots[-1][1]:
        snapshots.append(("Working tree", working_tree))
    return snapshots


def draw(snapshots, output):
    revisions, rows = zip(*snapshots)
    latest = rows[-1]
    if not latest:
        raise SystemExit("No formalization progress rows in README.md")

    figure, axes = plt.subplots(
        len(latest), sharex=True, squeeze=False, figsize=(11.3, 2 + 0.66 * len(latest)), facecolor=PAPER
    )
    figure.subplots_adjust(left=0.34, right=0.96, bottom=0.13, top=0.80, hspace=0.60)
    figure.text(0.04, 0.935, "Formalization progress", fontsize=25, weight="bold", color=INK)
    figure.text(0.04, 0.88, "Recorded README percentages by commit · Each row targets 100%", fontsize=12, color=MUTED)

    pending = revisions[-1] == "Working tree"
    commit_count = len(revisions) - pending
    for axis, (label, (latest_percent, latest_fraction)) in zip(axes.flat, latest.items()):
        values = [snapshot.get(label, (math.nan, None))[0] for snapshot in rows]
        axis.set_facecolor(PAPER)
        axis.set_ylim(-9, 112)
        axis.axhspan(0, 100, color="#f0f5ef", zorder=0)
        axis.axhline(100, color="#94a99b", linestyle=(0, (3, 3)), linewidth=0.9)
        axis.axhline(50, color="#dce7dd", linewidth=0.8)
        axis.axhline(0, color="#dce7dd", linewidth=0.8)
        axis.step(range(commit_count), values[:commit_count], where="post", color=GREEN, linewidth=1.8)
        for i, value in enumerate(values[:commit_count]):
            changed = i == 0 or rows[i].get(label) != rows[i - 1].get(label)
            axis.scatter(i, value, s=28 if changed else 13, color=GREEN, zorder=3)
        if pending:
            if commit_count:
                axis.step([commit_count - 1, commit_count], values[-2:], where="post",
                          color=GREEN, linewidth=1.4, linestyle="--")
            axis.scatter(commit_count, values[-1], s=30, facecolors=PAPER, edgecolors=GREEN, zorder=3)

        axis.text(-0.48, 0.68, label, transform=axis.transAxes, color=INK, fontsize=12, weight="bold")
        axis.text(-0.48, 0.27, f"{latest_percent}%  ({latest_fraction})", transform=axis.transAxes, color=GREEN, fontsize=11)
        axis.set_yticks([0, 100], labels=["0%", "100%"])
        axis.tick_params(axis="both", length=0, labelsize=9, colors=MUTED, pad=7)
        axis.spines[:].set_visible(False)

    last = len(revisions) - 1
    stride = max(1, math.ceil(last / 9))
    ticks = [*range(0, last - stride + 1, stride), last]
    axis = axes[-1, 0]
    axis.set_xlim(-0.15, len(revisions) - 0.85)
    axis.set_xticks(ticks, labels=[revisions[i] for i in ticks])
    axis.set_xlabel("Git history · oldest to newest", color=MUTED, fontsize=10, labelpad=12)
    figure.savefig(output, dpi=150, metadata={"Software": "tools/plot_progress.py"})
    plt.close(figure)


if __name__ == "__main__":
    draw(history(), ROOT / "docs/progress.png")
