import tempfile
import unittest
from pathlib import Path
from frontier import frontier, index

class FrontierTest(unittest.TestCase):
    def test_transitive_and_cycle(self):
        s = {"gaps": [
            {"id":"A","status":"open","depends_on":["C"]},
            {"id":"B","status":"blocked","depends_on":["A"]},
            {"id":"C","status":"open","depends_on":["B","missing"]},
            {"id":"D","status":"open"}]}
        r = frontier(s)
        self.assertEqual(r["ranking"][0], {"id":"A","score":2,"known_downstream":["B","C"]})
        self.assertEqual(r["unknown_edges"], [("C","missing")])
        self.assertEqual(r["missing_dependency_lists"], ["D"])
    def test_duplicate(self):
        with self.assertRaises(ValueError):
            frontier({"gaps":[{"id":"a"},{"id":"a"}]})
    def test_index(self):
        with tempfile.TemporaryDirectory() as d:
            Path(d,"x.lean").write_text("import Mathlib\nlemma foo : True := trivial\n")
            self.assertEqual(list(index(d))[0]["name"],"foo")
            self.assertEqual(list(index(d))[0]["line"],2)
