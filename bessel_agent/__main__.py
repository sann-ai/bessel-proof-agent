"""Run with python3 -m bessel_agent."""

import argparse
import json
import sys
from pathlib import Path

from .core import InputError, NeedsConditions, RECIPES, condition_labels, display_expr, load_json, replay, verify
from .parser import parse_identity


def main() -> int:
    parser = argparse.ArgumentParser(description="Check structured Bessel identities with Lean.")
    subparsers = parser.add_subparsers(dest="command", required=True)
    check = subparsers.add_parser("verify")
    check.add_argument("input", type=Path)
    check.add_argument("--output", type=Path, required=True)
    check.add_argument("--timeout", type=float, default=60)
    check.add_argument("--format", choices=("auto", "json", "text"), default="auto")
    check.add_argument("--conditions", help="For text input, for example: n integer, x > 0")
    check.add_argument("--recipe", choices=tuple(RECIPES))
    translate = subparsers.add_parser("parse", help="Translate a supported text/LaTeX equation into a fixed target.")
    translate.add_argument("input", type=Path)
    translate.add_argument("--conditions")
    translate.add_argument("--output", type=Path)
    again = subparsers.add_parser("replay")
    again.add_argument("directory", type=Path)
    again.add_argument("--timeout", type=float, default=60)
    args = parser.parse_args()
    if not 0 < getattr(args, "timeout", 60) <= 600:
        parser.error("--timeout must be positive and at most 600 seconds")
    try:
        if args.command == "parse":
            target = parse_identity(args.input.read_text(encoding="utf-8"), args.conditions)
            encoded = json.dumps(target, ensure_ascii=False, indent=2) + "\n"
            if args.output:
                with args.output.open("x", encoding="utf-8") as stream:
                    stream.write(encoded)
            print("正規化した式：" + display_expr(target["lhs"]) + " = " + display_expr(target["rhs"])
                  + "。条件：n は整数、x は実数、" + "、".join(condition_labels(target)) + "。", file=sys.stderr)
            print(encoded, end="")
            return 0
        if args.command == "replay":
            result = replay(args.directory, args.timeout)
        else:
            is_json = args.format == "json" or (args.format == "auto" and args.input.suffix.lower() == ".json")
            if is_json:
                if args.conditions:
                    raise InputError("JSON assumptions are fixed in the input; use --conditions with text input.")
                data = load_json(args.input)
            else:
                data = parse_identity(args.input.read_text(encoding="utf-8"), args.conditions)
                data["proof"] = {"mode": "direct", "recipe": args.recipe or "bessel"}
            if is_json and args.recipe:
                if not isinstance(data, dict) or "proof" in data:
                    raise InputError("Use --recipe only for a target JSON that has no proof candidate.")
                data["proof"] = {"mode": "direct", "recipe": args.recipe}
            result = verify(data, args.output, args.timeout)
    except NeedsConditions as exc:
        print(json.dumps({"status": "needs_conditions", "reason": str(exc)}, ensure_ascii=False))
        return 1
    except (InputError, OSError) as exc:
        print(json.dumps({"status": "unresolved", "reason": "input_or_environment_error",
                          "detail": str(exc)}, ensure_ascii=False))
        return 2
    print(json.dumps(result, ensure_ascii=False, indent=2))
    return 0 if result["status"] in {"proved", "refuted"} else 1


if __name__ == "__main__":
    raise SystemExit(main())
