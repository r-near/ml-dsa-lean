#!/usr/bin/env python3
"""Output stamps for the shell scripts (see common.py).

    stamp.py tool FILE...             print a digest of the contents of the files (the program that computes an output)
    stamp.py write OUT VEC TOOL       write OUT's stamp: the sha256 of VEC and the digest TOOL
    stamp.py check OUT VEC TOOL       exit 0 iff OUT exists and its stamp matches the current VEC and TOOL
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import digest_parts, sha256_file, stamp_ok, write_stamp  # noqa: E402


def main():
    cmd = sys.argv[1] if len(sys.argv) > 1 else ""
    if cmd == "tool" and len(sys.argv) > 2:
        print(digest_parts([sha256_file(f) for f in sys.argv[2:]]))
    elif cmd == "write" and len(sys.argv) == 5:
        write_stamp(sys.argv[2], sys.argv[3], sys.argv[4])
    elif cmd == "check" and len(sys.argv) == 5:
        sys.exit(0 if stamp_ok(sys.argv[2], sys.argv[3], sys.argv[4]) else 1)
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main()
