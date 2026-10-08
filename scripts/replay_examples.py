"""Recheck committed AI proof plans without invoking AI or reading credentials."""
from pathlib import Path
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from bessel_agent.core import replay

for route in ("direct", "steps", "recurrence-direct", "recurrence-steps"):
    path = ROOT / "demo" / route / "request.json"
    if not path.exists():
        raise SystemExit(f"Missing saved AI output: {path}")
    result = replay(path.parent, timeout=120)
    print(f"AI-generated {route}: {result['status']}")
    if result["status"] != "proved" or not result["replayed"]:
        raise SystemExit(json.dumps(result, ensure_ascii=False))
