"""Local, append-only evidence archive. Only replayed certificates are reusable."""
from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import tempfile
from typing import Any
import uuid

from .core import (ROOT, InputError, condition_labels, display_expr, environment,
                   load_json, normalized_conditions, replay, validate_request)

STATES = {"proved", "refuted", "unresolved", "needs_conditions"}
VERIFICATION_FILES = {"request.json", "result.json", "certificate.lean",
                      "proof_attempt.lean", "refutation_attempt.lean", "report.md"}
ENTRY_FILES = {"record.json", "request.json", "candidate.json", "original_input.txt", "detail.md"}
ENTRY_FILES |= {"verification/" + name for name in VERIFICATION_FILES}
RECORD_ID = re.compile(r"[a-f0-9]{32}\Z")


def resolve_archive_root(archive_root: Path | str | None = None) -> Path:
    chosen = archive_root if archive_root is not None else os.environ.get("BESSEL_ARCHIVE_DIR")
    root = Path(chosen).expanduser() if chosen else Path.home() / "BesselProofAgentData" / "archive"
    root = root.resolve()
    if root == ROOT.resolve() or ROOT.resolve() in root.parents:
        raise InputError("Archive data must be stored outside the application repository.")
    return root


def canonical_target(target: dict) -> dict:
    if not isinstance(target, dict):
        raise InputError("An archive target must be a structured JSON object.")
    result = dict(target)
    result.pop("proof", None)
    validate_request(result, require_proof=False)
    atoms = normalized_conditions(result)
    result.pop("extra_conditions", None)
    if atoms:
        result["extra_conditions"] = sorted(atoms, key=lambda atom: _json_bytes(atom))
    return result


def _json_bytes(value: Any) -> bytes:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"), allow_nan=False).encode("utf-8")


def _digest(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def target_hash(target: dict) -> str:
    return _digest(_json_bytes(canonical_target(target)))


def _target_or_none(request: Any) -> dict | None:
    if not isinstance(request, dict):
        return None
    try:
        return canonical_target(request)
    except InputError:
        return None


def _write(path: Path, raw: bytes) -> None:
    with path.open("xb") as stream:
        os.chmod(path, 0o600)
        stream.write(raw)
        stream.flush()
        os.fsync(stream.fileno())


def _write_json(path: Path, value: Any) -> None:
    _write(path, json.dumps(value, ensure_ascii=False, indent=2, allow_nan=False).encode("utf-8") + b"\n")


def _replace(path: Path, raw: bytes) -> None:
    descriptor, temporary = tempfile.mkstemp(prefix=".index-", dir=path.parent)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(raw)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def _input_summary(request: Any, original_input: str | None) -> tuple[str, list[str]]:
    target = _target_or_none(request)
    if target is not None:
        return display_expr(target["lhs"]) + " = " + display_expr(target["rhs"]), condition_labels(target)
    return (original_input or "入力を構造化できませんでした。")[:500], []


def _markdown_text(value: str) -> str:
    # Plain text prevents user input from introducing active links or HTML in the catalogue.
    return (value.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
            .replace("`", "&#96;").replace("[", "&#91;").replace("]", "&#93;")
            .replace("*", "&#42;").replace("_", "&#95;").replace("\n", " "))


def _details(record: dict, result: dict) -> str:
    labels = {"proved": "証明済み", "refuted": "反証済み", "unresolved": "未解決", "needs_conditions": "条件の確認待ち"}
    lines = [f"# {labels[record['status']]}", "", f"記録：{record['id']}", "",
             "保存日時：" + record["created_at"], "", "式：" + _markdown_text(record["expression"]), "",
             "条件：" + _markdown_text("、".join(record["conditions"]) or "元入力を確認してください。"), "",
             "命題ハッシュ：" + (record["target_sha256"] or "構造化前のため未付与"), "",
             "数学環境ハッシュ：" + record["environment_sha256"], ""]
    if record["status"] in {"proved", "refuted"}:
        lines += ["登録前に保存コピーをLeanで再検証しました。再利用時にも archive replay で検査します。", ""]
    else:
        lines += ["記録理由：" + _markdown_text(str(result.get("detail", result.get("reason", "検証が未完了です。")))), ""]
    lines += ["候補・結果・証明・元入力は、この記録のJSONとverificationディレクトリに保存しています。", ""]
    return "\n".join(lines)


def _load_record(entry: Path, expected_id: str | None = None) -> dict:
    record_id = expected_id or entry.name
    if entry.is_symlink() or not entry.is_dir() or not RECORD_ID.fullmatch(record_id):
        raise InputError("Invalid archive entry path.")
    manifest_path = entry / "manifest.json"
    if manifest_path.is_symlink():
        raise InputError("Archive manifests cannot be symbolic links.")
    manifest = load_json(manifest_path)
    if not isinstance(manifest, dict) or set(manifest) != {"schema_version", "files"} or manifest["schema_version"] != 1:
        raise InputError("Invalid archive manifest.")
    files = manifest["files"]
    if not isinstance(files, dict) or set(files) - ENTRY_FILES or not {"record.json", "detail.md", "verification/result.json"} <= set(files):
        raise InputError("Invalid archive manifest file list.")
    actual = set()
    for path in entry.rglob("*"):
        if path.is_symlink():
            raise InputError("Archive entries cannot contain symbolic links.")
        if path.is_file() and path.relative_to(entry).as_posix() != "manifest.json":
            actual.add(path.relative_to(entry).as_posix())
    if actual != set(files):
        raise InputError("Archive entry files changed after registration.")
    for relative, digest in files.items():
        if _digest((entry / relative).read_bytes()) != digest:
            raise InputError(f"Archive evidence changed after registration: {relative}")
    record = load_json(entry / "record.json")
    if (not isinstance(record, dict) or record.get("schema_version") != 1 or record.get("id") != record_id
            or not isinstance(record.get("status"), str) or record["status"] not in STATES
            or not isinstance(record.get("expression"), str) or not isinstance(record.get("created_at"), str)
            or not isinstance(record.get("conditions"), list)
            or any(not isinstance(item, str) for item in record["conditions"])):
        raise InputError("Invalid archive record metadata.")
    request = load_json(entry / "request.json") if "request.json" in files else None
    result = load_json(entry / "verification/result.json")
    if not isinstance(result, dict) or result.get("status") != record["status"]:
        raise InputError("Archive record and verification status disagree.")
    if "verification/request.json" in files and load_json(entry / "verification/request.json") != request:
        raise InputError("Archive request and verification target disagree.")
    canonical = _target_or_none(request)
    key = _digest(_json_bytes(canonical)) if canonical is not None else None
    if record.get("target_sha256") != key:
        raise InputError("Archive target hash and request disagree.")
    if record.get("environment_sha256") != _digest(_json_bytes(record.get("environment"))):
        raise InputError("Archive environment hash is inconsistent.")
    if record["status"] in {"proved", "refuted"} and not {"verification/request.json", "verification/certificate.lean"} <= set(files):
        raise InputError("An accepted archive record requires its complete certificate.")
    candidate = load_json(entry / "candidate.json") if "candidate.json" in files else None
    if isinstance(request, dict) and "proof" in request and request["proof"] != candidate:
        raise InputError("Archive candidate and request disagree.")
    original = (entry / "original_input.txt").read_text(encoding="utf-8") if "original_input.txt" in files else None
    return {**record, "request": request, "candidate": candidate, "original_input": original,
            "canonical_target": canonical, "verification_dir": str(entry / "verification"),
            "record_dir": str(entry), "result": result}


def _index(root: Path, records: list[dict]) -> None:
    summaries = [{key: record[key] for key in ("id", "created_at", "status", "target_sha256", "expression", "conditions")}
                 for record in records]
    _replace(root / "index.json", _json_bytes({"schema_version": 1, "records": summaries}) + b"\n")
    lines = ["# ベッセル恒等式の検証記録", "", "各項目は試行ごとの記録です。同じ命題の再試行も別々に保持します。", ""]
    for record in summaries:
        lines += [f"- [{record['id']}](entries/{record['id']}/detail.md) — {record['status']} — "
                  + _markdown_text(record["expression"]),
                  "  条件：" + _markdown_text("、".join(record["conditions"]) or "元入力を確認"), ""]
    _replace(root / "catalog.md", "\n".join(lines).encode("utf-8"))


def list_records(archive_root: Path | str | None = None) -> list[dict]:
    root = resolve_archive_root(archive_root)
    if not root.exists():
        return []
    entries = root / "entries"
    if entries.is_symlink():
        raise InputError("The archive entries directory cannot be a symbolic link.")
    records = []
    if entries.exists():
        for entry in sorted(entries.iterdir()):
            if entry.name.startswith(".pending-"):
                continue
            records.append(_load_record(entry))
    records.sort(key=lambda record: (record["created_at"], record["id"]), reverse=True)
    _index(root, records)  # Entries are authoritative; stale/corrupt indexes are rebuilt.
    return records


def show_record(record_id: str, archive_root: Path | str | None = None) -> dict:
    if not isinstance(record_id, str) or not RECORD_ID.fullmatch(record_id):
        raise InputError("Use the complete 32-character archive record ID.")
    root = resolve_archive_root(archive_root)
    if (root / "entries").is_symlink():
        raise InputError("The archive entries directory cannot be a symbolic link.")
    return _load_record(root / "entries" / record_id)


def search_records(query: str, archive_root: Path | str | None = None) -> list[dict]:
    query = query.casefold()
    return [record for record in list_records(archive_root)
            if query in " ".join([record["id"], record["expression"], record["status"], *record["conditions"]]).casefold()]


def find_exact(target: dict, archive_root: Path | str | None = None) -> list[dict]:
    canonical = canonical_target(target)
    key = _digest(_json_bytes(canonical))
    return [record for record in list_records(archive_root)
            if record["target_sha256"] == key and record["canonical_target"] == canonical]


def replay_record(record_id: str, archive_root: Path | str | None = None, timeout: float = 60) -> dict:
    record = show_record(record_id, archive_root)
    result = replay(Path(record["verification_dir"]), timeout)
    return {**result, "record_id": record_id}


def _register(*, directory: Path | None, result: dict | None, archive_root: Path | str | None,
              original_input: str | None, input_conditions: Any, request: Any,
              candidate: Any, provenance: dict | None, timeout: float) -> dict:
    root = resolve_archive_root(archive_root)
    root.mkdir(parents=True, exist_ok=True, mode=0o700)
    entries = root / "entries"
    if entries.is_symlink():
        raise InputError("The archive entries directory cannot be a symbolic link.")
    entries.mkdir(exist_ok=True, mode=0o700)
    # Fail before adding anything if an existing registered record is damaged.
    list_records(root)
    pending = Path(tempfile.mkdtemp(prefix=".pending-", dir=entries))
    try:
        verification = pending / "verification"
        verification.mkdir(mode=0o700)
        if directory is not None:
            for name in sorted(VERIFICATION_FILES):
                source = directory / name
                if source.is_symlink():
                    raise InputError("Verification evidence cannot be a symbolic link.")
                if source.exists():
                    if not source.is_file() or source.stat().st_size > 8 * 1024 * 1024:
                        raise InputError("Verification evidence must be a regular file below 8 MiB.")
                    _write(verification / name, source.read_bytes())
            result = load_json(verification / "result.json")
            if (verification / "request.json").exists():
                saved_request = load_json(verification / "request.json")
                if request is not None and request != saved_request:
                    raise InputError("The supplied request differs from the verification evidence.")
                request = saved_request
        else:
            _write_json(verification / "result.json", result)
        if not isinstance(result, dict) or not isinstance(result.get("status"), str) or result["status"] not in STATES:
            raise InputError("Archive status must be proved, refuted, unresolved, or needs_conditions.")
        if result["status"] in {"proved", "refuted"}:
            checked = replay(verification, timeout)
            if not checked.get("replayed") or checked.get("status") != result["status"]:
                raise InputError("The certificate did not pass replay before archive registration.")
        canonical = _target_or_none(request)
        if request is not None:
            _write_json(pending / "request.json", request)
        if isinstance(request, dict) and "proof" in request:
            if candidate is not None and candidate != request["proof"]:
                raise InputError("The candidate differs from the supplied request.")
            candidate = request["proof"]
        if candidate is not None:
            _write_json(pending / "candidate.json", candidate)
        if original_input is not None:
            if not isinstance(original_input, str) or len(original_input.encode("utf-8")) > 1024 * 1024:
                raise InputError("Archived original input must be UTF-8 text below 1 MiB.")
            _write(pending / "original_input.txt", original_input.encode("utf-8"))
        expression, conditions = _input_summary(request, original_input)
        recorded_environment = result.get("environment", environment())
        record = {"schema_version": 1, "id": uuid.uuid4().hex,
                  "created_at": datetime.now(timezone.utc).isoformat(), "status": result["status"],
                  "target_sha256": _digest(_json_bytes(canonical)) if canonical is not None else None,
                  "expression": expression, "conditions": conditions, "input_conditions": input_conditions,
                  "provenance": provenance,
                  "environment": recorded_environment,
                  "environment_sha256": _digest(_json_bytes(recorded_environment))}
        _write_json(pending / "record.json", record)
        _write(pending / "detail.md", _details(record, result).encode("utf-8"))
        files = {path.relative_to(pending).as_posix(): _digest(path.read_bytes())
                 for path in pending.rglob("*") if path.is_file()}
        _write_json(pending / "manifest.json", {"schema_version": 1, "files": files})
        destination = entries / record["id"]
        _load_record(pending, expected_id=record["id"])
        os.rename(pending, destination)
        registered = _load_record(destination)
        list_records(root)
        return registered
    finally:
        if pending.exists():
            shutil.rmtree(pending)


def register_verification(directory: Path, archive_root: Path | str | None = None, *,
                          original_input: str | None = None, input_conditions: Any = None,
                          request: Any = None, provenance: dict | None = None, timeout: float = 60) -> dict:
    return _register(directory=Path(directory), result=None, archive_root=archive_root,
                     original_input=original_input, input_conditions=input_conditions,
                     request=request, candidate=None, provenance=provenance, timeout=timeout)


def register_failure(result: dict, archive_root: Path | str | None = None, *,
                     original_input: str | None = None, input_conditions: Any = None,
                     request: Any = None, candidate: Any = None, provenance: dict | None = None) -> dict:
    if not isinstance(result, dict) or not isinstance(result.get("status"), str) or result["status"] not in {"unresolved", "needs_conditions"}:
        raise InputError("A failure record must be unresolved or needs_conditions.")
    return _register(directory=None, result=result, archive_root=archive_root,
                     original_input=original_input, input_conditions=input_conditions,
                     request=request, candidate=candidate, provenance=provenance, timeout=60)
