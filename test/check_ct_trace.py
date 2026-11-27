"""Check Memcheck reports against the reviewed record-opening branches."""

import sys
from collections import defaultdict
from pathlib import Path
from xml.etree import ElementTree


ROOT = Path(__file__).resolve().parent.parent
TLS = ROOT / "_build/c/Tls_Conn.c"
CHACHA = ROOT / "csrc/hacl/Hacl_AEAD_Chacha20Poly1305.c"
REVIEWED_BRANCHES = {
    (CHACHA, "Hacl_AEAD_Chacha20Poly1305_decrypt", "if (z == 255U)"): "authentication result",
    (TLS, "unseal", "if (r == 0U)"): "authentication result",
    (TLS, "Tls_Crypto_last_nz", "if (c != 0U)"): "inner content-type scan",
}


def check_report(report):
    root = ElementTree.parse(report).getroot()
    states = root.findall("status/state")
    if root.findtext("tool") != "memcheck" or not states or states[-1].text != "FINISHED":
        sys.exit(f"Incomplete Memcheck report in {report}")

    source_lines = {path: path.read_text().splitlines() for path in (TLS, CHACHA)}
    counts = {
        pair.findtext("unique"): int(pair.findtext("count"))
        for pair in root.findall("errorcounts/pair")
    }
    reviewed = defaultdict(list)
    unexpected = 0
    for error in root.findall("error"):
        frames = error.findall("stack[1]/frame")
        site = frames[0] if frames else ElementTree.Element("frame")
        path = Path(site.findtext("dir", ""), site.findtext("file", "")).resolve()
        function = site.findtext("fn", "unknown function")
        line = int(site.findtext("line", "0"))
        lines = source_lines.get(path, [])

        # Match the instruction's own source statement, including inlined frames.
        # An error further down the stack in the same function is still an error.
        if (error.findtext("kind") == "UninitCondition"
                and 0 < line <= len(lines)
                and any(frame.findtext("fn") == "Tls_Conn_open_rec" for frame in frames[1:])):
            branch = REVIEWED_BRANCHES.get((path, function, lines[line - 1].strip()))
            if branch:
                reviewed[branch].append(counts[error.findtext("unique")])
                continue

        unexpected += 1
        description = error.findtext("what") or error.findtext("xwhat/text") or error.findtext("kind")
        print(f"{path}:{line}: {function}: {description}", file=sys.stderr)

    for branch, events in reviewed.items():
        print(f"Reviewed Memcheck contexts for {branch}: {len(events)} ({sum(events)} events)")
    print(f"Unexpected Memcheck contexts: {unexpected}. Full report: {report}")
    return unexpected != 0


if __name__ == "__main__":
    sys.exit(check_report(Path(sys.argv[1])))
