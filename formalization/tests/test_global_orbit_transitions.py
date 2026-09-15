"""Test producer failure handling; generated data still requires Lean proofs."""
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


@unittest.skipUnless(shutil.which("c++"), "C++ compiler required")
class TransitionProducerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory()
        cls.binary = Path(cls.directory.name) / "producer"
        source = Path(__file__).resolve().parents[1] / "tools/global_orbit_transitions.cpp"
        subprocess.run(["c++", "-O2", "-std=c++17", "-Wall", "-Wextra",
                        str(source), "-o", str(cls.binary)], check=True)

    @classmethod
    def tearDownClass(cls):
        cls.directory.cleanup()

    def run_producer(self, text):
        return subprocess.run([str(self.binary)], input=text, text=True,
                              capture_output=True, timeout=30)

    def test_top_and_hyperplanes_close_under_extensions(self):
        bases = [[256, 128, 64, 32, 16, 8, 4, 2, 1],
                 [128, 64, 32, 16, 8, 4, 2, 1],
                 [256, 160, 64, 16, 8, 4, 2, 1],
                 [256, 128, 68, 32, 20, 8, 2, 1]]
        raw = "4\n" + "\n".join(f"{len(b)} " + " ".join(map(str, b)) for b in bases)
        result = self.run_producer(raw)
        self.assertEqual(result.returncode, 0, result.stderr)
        rows = [json.loads(line) for line in result.stdout.splitlines()]
        self.assertEqual([r["size"] for r in rows[:4]], [1, 49, 294, 168])
        self.assertEqual(rows[-1], {"complete": True, "spaces": 512, "extensions": 3})
        for row in rows[4:-1]:
            source = [row["code"], *bases[row["source"]]]
            target = bases[row["target"]]
            self.assertEqual(row["word"], [])
            self.assertEqual(len(row["forward"]), len(source))
            self.assertEqual(len(row["backward"]), len(target))
            def xor_selected(basis, mask):
                value = 0
                for i, code in enumerate(basis):
                    if mask >> i & 1:
                        value ^= code
                return value
            self.assertEqual([xor_selected(target, m) for m in row["forward"]], source)
            self.assertEqual([xor_selected(source, m) for m in row["backward"]], target)

    def test_invalid_or_incomplete_inputs_do_not_claim_completion(self):
        for raw in ("", "0", "1\n10", "1\n2 1 1", "1\n1 512", "1\n1",
                    "1\n0\ntrailing", "2\n0\n0", "1\n0"):
            with self.subTest(raw=raw):
                result = self.run_producer(raw)
                self.assertNotEqual(result.returncode, 0)
                self.assertNotIn('"complete":true', result.stdout)
                self.assertIn("FAILED:", result.stderr)

    def test_arbitrary_queries_preserve_supplied_generator_order(self):
        bases = [[256, 128, 64, 32, 16, 8, 4, 2, 1],
                 [128, 64, 32, 16, 8, 4, 2, 1],
                 [256, 160, 64, 16, 8, 4, 2, 1],
                 [256, 128, 68, 32, 20, 8, 2, 1]]
        raw = "4\n" + "\n".join(f"{len(b)} " + " ".join(map(str, b)) for b in bases)
        queries = [[1, 2, 4, 8, 16, 32, 64, 256], list(reversed(bases[2]))]
        path = Path(self.directory.name) / "queries.txt"
        path.write_text("2\n" + "\n".join("8 " + " ".join(map(str, b)) for b in queries))
        result = subprocess.run([str(self.binary), "--queries", str(path)], input=raw,
                                text=True, capture_output=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stderr)
        records = [json.loads(line) for line in result.stdout.splitlines()]
        self.assertEqual(records[-1], {"complete": True, "spaces": 512, "queries": 2})

        def transform(g, x):
            a = [[(x >> (3 * i + j)) & 1 for j in range(3)] for i in range(3)]
            if g == 0:
                a[0], a[1] = a[1], a[0]
            elif g == 1:
                a[1], a[2] = a[2], a[1]
            elif g == 2:
                a[0] = [u ^ v for u, v in zip(a[0], a[1])]
            else:
                a = list(zip(*a))
            return sum(a[i][j] << (3 * i + j) for i in range(3) for j in range(3))

        def xor_selected(basis, mask):
            value = 0
            self.assertLess(mask, 1 << len(basis))
            for k, c in enumerate(basis):
                if mask >> k & 1:
                    value ^= c
            return value

        self.assertEqual([r["query"] for r in records[4:-1]], [0, 1])
        self.assertTrue(any(r["word"] for r in records[4:-1]))
        for row in records[4:-1]:
            source = queries[row["query"]]
            target = bases[row["target"]]
            for g in reversed(row["word"]):
                target = [transform(g, x) for x in target]
            self.assertEqual([xor_selected(target, m) for m in row["forward"]], source)
            self.assertEqual([xor_selected(source, m) for m in row["backward"]], target)

    def test_bad_or_uncovered_queries_fail(self):
        path = Path(self.directory.name) / "bad-queries.txt"
        for query in ("", "0", "1\n2 1 1", "1\n1 512", "1\n0", "1\n9 1 2"):
            with self.subTest(query=query):
                path.write_text(query)
                result = subprocess.run([str(self.binary), "--queries", str(path)],
                                        input="1\n9 256 128 64 32 16 8 4 2 1\n",
                                        text=True, capture_output=True, timeout=30)
                self.assertNotEqual(result.returncode, 0)
                self.assertNotIn('"complete":true', result.stdout)


if __name__ == "__main__":
    unittest.main()
