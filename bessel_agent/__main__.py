"""Run with python3 -m bessel_agent."""

import argparse
import json
from pathlib import Path

from .core import InputError, load_json, replay, verify


def main() -> int:
    parser = argparse.ArgumentParser(description="Check structured Bessel identities with Lean.")
    subparsers = parser.add_subparsers(dest="command", required=True)
    check = subparsers.add_parser("verify")
    check.add_argument("input", type=Path)
    check.add_argument("--output", type=Path, required=True)
    check.add_argument("--timeout", type=float, default=60)
    again = subparsers.add_parser("replay")
    again.add_argument("directory", type=Path)
    again.add_argument("--timeout", type=float, default=60)
    args = parser.parse_args()
    if not 0 < args.timeout <= 600:
        parser.error("--timeout must be positive and at most 600 seconds")
    try:
        result = (verify(load_json(args.input), args.output, args.timeout)
                  if args.command == "verify" else replay(args.directory, args.timeout))
    except (InputError, OSError) as exc:
        print(json.dumps({"status": "unresolved", "reason": "input_or_environment_error",
                          "detail": str(exc)}, ensure_ascii=False))
        return 2
    print(json.dumps(result, ensure_ascii=False, indent=2))
    return 0 if result["status"] in {"proved", "refuted"} else 1


if __name__ == "__main__":
    raise SystemExit(main())
