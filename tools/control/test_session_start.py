import json
import tempfile
import unittest
from datetime import datetime, timedelta, timezone
from pathlib import Path
from unittest.mock import patch
from session_start import frontier, lean_probe, UPSTREAM, TOOLCHAIN, LEAN_COMMIT


class PreflightTests(unittest.TestCase):
    def test_frontier(self):
        now = datetime(2026, 11, 24, tzinfo=timezone.utc)
        base = dict(observed_at=now.isoformat(), upstream_repository=UPSTREAM,
                    upstream_sha="a" * 40, toolchain=TOOLCHAIN, gaps=[])
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "index.json"
            self.assertEqual(frontier(p, now)["state"], "unavailable")
            for edits, expected in [({}, "fresh_public_snapshot"),
                ({"observed_at": (now - timedelta(seconds=1201)).isoformat()}, "unavailable"),
                ({"observed_at": (now + timedelta(seconds=1)).isoformat()}, "unavailable"),
                ({"observed_at": now.replace(tzinfo=None).isoformat()}, "unavailable"),
                ({"upstream_repository": "other/repo"}, "unavailable"),
                ({"upstream_sha": "main"}, "unavailable"),
                ({"toolchain": "wrong"}, "unavailable"),
                ({"gaps": {}}, "unavailable")]:
                p.write_text(json.dumps(base | edits))
                with self.subTest(edits=edits):
                    self.assertEqual(frontier(p, now)["state"], expected)
            p.write_text("null")
            self.assertEqual(frontier(p, now)["state"], "unavailable")

    def test_lean(self):
        with patch("session_start.run", side_effect=[LEAN_COMMIT, "Lean", "Lake", ""]):
            self.assertEqual(lean_probe(Path("/unused"))["state"], "core_checked")
        with patch("session_start.run", return_value="wrong"):
            self.assertEqual(lean_probe(Path("/unused"))["state"], "unavailable")
        with patch("session_start.run", side_effect=FileNotFoundError):
            self.assertEqual(lean_probe(Path("/unused"))["state"], "unavailable")


if __name__ == "__main__":
    unittest.main()
