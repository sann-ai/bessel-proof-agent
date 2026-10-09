"""Inspect the pinned local environment without installing tools or running AI."""
from __future__ import annotations

import json
import importlib.util
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def run(command: list[str], root: Path) -> tuple[bool, str]:
    try:
        result = subprocess.run(command, cwd=root, capture_output=True, text=True, timeout=15)
    except (OSError, subprocess.TimeoutExpired) as exc:
        return False, str(exc)
    return result.returncode == 0, (result.stdout or result.stderr).strip()


def inspect(root: Path = ROOT) -> list[tuple[bool, str]]:
    checks = [(sys.version_info >= (3, 12), f"Python {sys.version.split()[0]}（必要版: 3.12以上）")]
    if not checks[0][0]:
        return checks
    import tomllib

    try:
        toolchain = (root / "lean-toolchain").read_text().strip()
        manifest = json.loads((root / "lake-manifest.json").read_text())
        config = tomllib.loads((root / "lakefile.toml").read_text())
        declared = next(item["rev"] for item in config["require"] if item["name"] == "mathlib")
        locked = next(item["rev"] for item in manifest["packages"] if item["name"] == "mathlib")
    except (OSError, ValueError, KeyError, StopIteration) as exc:
        return checks + [(False, f"固定環境ファイルを確認してください: {exc}")]
    checks.append((declared == locked, "lakefile.toml と lake-manifest.json の mathlib 固定版"))
    git = shutil.which("git")
    elan = shutil.which("elan")
    checks.append((git is not None, "Git（ZIPからの利用でも依存取得に必要）"))
    checks.append((elan is not None, "elan（未導入の場合は docs/setup.md を参照）"))
    if elan:
        # `elan run` only installs a missing toolchain when --install is supplied.
        for command in ("lean", "lake"):
            ok, output = run([elan, "run", toolchain, command, "--version"], root)
            checks.append((ok, f"{toolchain} の {command}: {output}"))
    missing, mismatched = [], []
    for package in manifest["packages"]:
        directory = root / ".lake" / "packages" / package["name"]
        if not directory.is_dir():
            missing.append(package["name"])
        elif git:
            ok, revision = run([git, "-C", str(directory), "rev-parse", "HEAD"], root)
            if not ok or revision != package["rev"]:
                mismatched.append(package["name"])
    checks.append((not missing, "取得済み依存" + (f"（未取得: {', '.join(missing)}）" if missing else "")))
    checks.append((git is not None and not missing and not mismatched, "依存コミットと lockfile の一致" +
                   (f"（要確認: {', '.join(mismatched)}）" if mismatched else
                    "（Git・依存の準備後に確認）" if git is None or missing else "")))
    checks.append(((root / ".lake/build/lib/lean/BesselProofAgent.olean").is_file(),
                   "プロジェクトのビルド出力（ソース更新後は lake build で更新）"))
    return checks


def main() -> int:
    checks = inspect()
    for ok, message in checks:
        print(f"{'OK' if ok else '要準備'}: {message}")
    print("保存証明の検査にAI認証は不要です。準備・更新手順: docs/setup.md")
    print("個人記録の既定保存先: ~/BesselProofAgentData/archive（この診断では作成しません）")
    backend = importlib.util.find_spec("mpmath")
    print("数値診断v2: " + ("既存mpmathを利用可能" if backend else
          "mpmath未導入のため backend_unavailable。構造化・解析テンプレート・条件付きLean・archiveは利用可能"))
    return 0 if all(ok for ok, _ in checks) else 1


if __name__ == "__main__":
    raise SystemExit(main())
