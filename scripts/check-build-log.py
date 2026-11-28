#!/usr/bin/env python3
"""Reject unexpected info diagnostics from project sources in a Lake build log."""

import re
import sys
from pathlib import Path

SOURCE_INFO = re.compile(r"^info: (?:\./)?(src/.+\.lean):[0-9]+:[0-9]+:(.*)")
# Allow one matching message regardless of its source position. Remove after #9138.
KNOWN_INFO = (
    "src/New/Spanning/MainTerm/GlobalSieve.lean",
    " Try this:",
    "  [apply] ring_nf",
)


def main():
    log = Path(sys.argv[1]).read_text(encoding="utf-8").splitlines()
    unexpected = []
    known_info_seen = False
    for line, following in zip(log, log[1:] + [""]):
        diagnostic = SOURCE_INFO.match(line)
        if diagnostic is None:
            continue
        if not known_info_seen and (*diagnostic.groups(), following) == KNOWN_INFO:
            known_info_seen = True
            continue
        unexpected.append(line)
    if not unexpected:
        return 0

    print(*unexpected, sep="\n", file=sys.stderr)
    print(
        "::error::Project modules report unexpected info diagnostics. "
        "Resolve tactic suggestions or guard expected command output with #guard_msgs.",
        file=sys.stderr,
    )
    return 1


if __name__ == "__main__":
    sys.exit(main())
