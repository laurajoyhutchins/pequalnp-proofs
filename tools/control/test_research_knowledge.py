import hashlib
import unittest
from research_knowledge import graph, reachable, normalized_detail, join_packet

def h(s):return "sha256:"+hashlib.sha256(s.encode()).hexdigest()
class KnowledgeTests(unittest.TestCase):
    def setUp(self):
        self.nodes=graph([{"key":"meta","program":"meta_complexity","nodes":[
            [1,"c",[],"a"*12,0,0,0],[2,"j",[1,"L-lib-003"],"b"*12,0,0,0],
            [4,"j",[2],"d"*12,0,0,0]]},{"key":"lib","program":"library","nodes":[[3,"c",[],"c"*12,0,0,0]]}])
    def detail(self):
        return {"id":"L-meta-002","program":"meta_complexity","title":"Example",
                "formal_statement":"True","statement_hash":h("True"),"status":"conjecture",
                "depends_on":["L-meta-001","L-lib-003"],"used_by":["L-meta-004"],
                "attempts":[{"outcome":"died","why_died":"counterexample","private":"not copied"}]}
    def test_edges(self):
        self.assertEqual(self.nodes["L-meta-002"]["depends_on"],["L-meta-001","L-lib-003"])
        self.assertEqual(reachable(self.nodes,"L-meta-001"),["L-meta-002","L-meta-004"])
    def test_exact_join(self):
        n=self.nodes["L-meta-002"];d=normalized_detail(self.detail(),n)
        x=join_packet({"statement":"True"},n,d,{},self.nodes)
        self.assertEqual(x["join"],"exact_statement")
        self.assertEqual(x["attempts"],[{"outcome":"died","why_died":"counterexample"}])
        self.assertIsNone(x["prerequisites"][0]["status"])
        self.assertEqual(join_packet({"statement":"False"},n,d,{},self.nodes)["join"],"statement_mismatch")
    def test_fail_closed(self):
        n=self.nodes["L-meta-002"];d=self.detail();d["used_by"]=[]
        self.assertEqual(join_packet({"statement":"True"},n,normalized_detail(d,n),{},self.nodes)["join"],"graph_detail_disagreement")
        d=self.detail();d["statement_hash"]=h("False")
        self.assertEqual(join_packet({"statement":"True"},n,normalized_detail(d,n),{},self.nodes)["join"],"statement_mismatch")
        self.assertIsNone(join_packet({"statement":"True"},None,None,{},self.nodes)["depends_on"])
    def test_invalid_graph(self):
        with self.assertRaises(ValueError):
            graph([{"key":"meta","program":"meta_complexity","nodes":[[1,"j",["bad"],"a"*12,0,0,0]]}])
if __name__=="__main__":unittest.main()
