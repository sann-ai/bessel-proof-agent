"""Run with python3 -m bessel_agent."""

import argparse
import json
import sys
from pathlib import Path

from .core import InputError, NeedsConditions, RECIPES, condition_labels, display_expr, load_json, replay, verify
from .parser import parse_identity
from . import archive


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
    for command in (check, translate):
        command.add_argument("--archive", action="store_true", help="Save this attempt in the local evidence archive.")
        command.add_argument("--archive-dir", type=Path)
    saved = subparsers.add_parser("archive", help="Manage the external local evidence archive.")
    operations = saved.add_subparsers(dest="archive_command", required=True)
    for operation in ("add", "list", "search", "show", "replay"):
        command = operations.add_parser(operation)
        command.add_argument("--archive-dir", type=Path)
        if operation in {"add", "replay"}:
            command.add_argument("--timeout", type=float, default=60)
        if operation == "add":
            command.add_argument("directory", type=Path)
            command.add_argument("--original-input", type=Path)
        elif operation == "search":
            command.add_argument("query")
        elif operation in {"show", "replay"}:
            command.add_argument("record_id")
    again = subparsers.add_parser("replay")
    again.add_argument("directory", type=Path)
    again.add_argument("--timeout", type=float, default=60)
    args = parser.parse_args()
    if not 0 < getattr(args, "timeout", 60) <= 600:
        parser.error("--timeout must be positive and at most 600 seconds")
    if args.command in {"parse", "verify"} and args.archive_dir is not None and not args.archive:
        parser.error("--archive-dir requires --archive")
    data = None
    original_input = None

    def save_failure(result):
        if getattr(args, "archive", False):
            try:
                record = archive.register_failure(result, args.archive_dir, original_input=original_input,
                                                  input_conditions=getattr(args, "conditions", None), request=data)
                result = {**result, "archive_id": record["id"]}
            except (InputError, OSError, ValueError) as exc:
                result = {**result, "archive_error": str(exc)}
        return result

    try:
        if args.command == "archive":
            root = args.archive_dir
            operation = args.archive_command
            if operation == "add":
                raw = args.original_input.read_text(encoding="utf-8") if args.original_input else None
                record = archive.register_verification(args.directory, root, original_input=raw, timeout=args.timeout)
                result = {"archive_id": record["id"], "status": record["status"], "target_sha256": record["target_sha256"]}
            elif operation in {"list", "search"}:
                records = archive.list_records(root) if operation == "list" else archive.search_records(args.query, root)
                result = [{key: record[key] for key in ("id", "created_at", "status", "target_sha256", "expression", "conditions")}
                          for record in records]
            elif operation == "show":
                result = archive.show_record(args.record_id, root)
            else:
                result = archive.replay_record(args.record_id, root, args.timeout)
            print(json.dumps(result, ensure_ascii=False, indent=2))
            return 1 if operation == "replay" and not result.get("replayed") else 0
        if args.command in {"parse", "verify"}:
            original_input = args.input.read_text(encoding="utf-8")
        if args.command == "parse":
            target = parse_identity(original_input, args.conditions)
            data = target
            encoded = json.dumps(target, ensure_ascii=False, indent=2) + "\n"
            if args.output:
                with args.output.open("x", encoding="utf-8") as stream:
                    stream.write(encoded)
            print("正規化した式：" + display_expr(target["lhs"]) + " = " + display_expr(target["rhs"])
                  + "。条件：n は整数、x は実数、" + "、".join(condition_labels(target)) + "。", file=sys.stderr)
            if args.archive:
                record = archive.register_failure({"status": "unresolved", "reason": "parsed_input_only"},
                                                  args.archive_dir, request=target, original_input=original_input,
                                                  input_conditions=args.conditions)
                print("保存した記録：" + record["id"], file=sys.stderr)
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
                data = parse_identity(original_input, args.conditions)
                data["proof"] = {"mode": "direct", "recipe": args.recipe or "bessel"}
            if is_json and args.recipe:
                if not isinstance(data, dict) or "proof" in data:
                    raise InputError("Use --recipe only for a target JSON that has no proof candidate.")
                data["proof"] = {"mode": "direct", "recipe": args.recipe}
            result = verify(data, args.output, args.timeout)
            if args.archive:
                record = archive.register_verification(args.output, args.archive_dir, original_input=original_input,
                                                       input_conditions=args.conditions, request=data, timeout=args.timeout)
                result = {**result, "archive_id": record["id"]}
    except NeedsConditions as exc:
        print(json.dumps(save_failure({"status": "needs_conditions", "reason": str(exc)}), ensure_ascii=False))
        return 1
    except (InputError, OSError, UnicodeError) as exc:
        print(json.dumps(save_failure({"status": "unresolved", "reason": "input_or_environment_error",
                                       "detail": str(exc)}), ensure_ascii=False))
        return 2
    print(json.dumps(result, ensure_ascii=False, indent=2))
    return 0 if result["status"] in {"proved", "refuted"} else 1


if __name__ == "__main__":
    raise SystemExit(main())
