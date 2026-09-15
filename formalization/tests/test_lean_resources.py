"""Stack-limit tests never change the test runner's resource limits."""
from pathlib import Path
import sys
import unittest
from unittest.mock import Mock, patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import lean_resources


class LeanResourceTests(unittest.TestCase):
    def limits(self, soft, hard, after=None):
        api = Mock(RLIMIT_STACK=3, RLIM_INFINITY=-1)
        api.getrlimit.side_effect = [(soft, hard), after or (soft, hard)]
        return api

    def test_small_soft_limit_is_raised_and_hard_limit_preserved(self):
        for hard in (-1, lean_resources.MIN_STACK_BYTES):
            with self.subTest(hard=hard):
                api = self.limits(8 * 1024 * 1024, hard,
                                  (lean_resources.MIN_STACK_BYTES, hard))
                with patch.object(lean_resources, "resource", api):
                    record = lean_resources.configure_process_stack()
                api.setrlimit.assert_called_once_with(
                    api.RLIMIT_STACK, (lean_resources.MIN_STACK_BYTES, hard))
                self.assertEqual(record["before"], {"soft": 8 * 1024 * 1024, "hard": hard})
                self.assertEqual(record["after"],
                                 {"soft": lean_resources.MIN_STACK_BYTES, "hard": hard})
                self.assertTrue(record["supported"])
                self.assertTrue(record["changed"])

    def test_sufficient_and_unlimited_soft_limits_are_not_lowered(self):
        for soft in (-1, lean_resources.MIN_STACK_BYTES, 2 * lean_resources.MIN_STACK_BYTES):
            with self.subTest(soft=soft):
                api = self.limits(soft, -1)
                with patch.object(lean_resources, "resource", api):
                    record = lean_resources.configure_process_stack()
                api.setrlimit.assert_not_called()
                self.assertEqual(record["before"], record["after"])
                self.assertFalse(record["changed"])

    def test_small_hard_limit_fails_without_changing_it(self):
        api = self.limits(8 * 1024 * 1024, 64 * 1024 * 1024)
        with patch.object(lean_resources, "resource", api):
            with self.assertRaisesRegex(RuntimeError, "hard limit.*256 MiB"):
                lean_resources.configure_process_stack()
        api.setrlimit.assert_not_called()

    def test_setrlimit_failure_has_actionable_diagnostic(self):
        for error in (OSError("denied"), ValueError("denied")):
            with self.subTest(error=type(error).__name__):
                api = self.limits(8 * 1024 * 1024, -1)
                api.setrlimit.side_effect = error
                with patch.object(lean_resources, "resource", api):
                    with self.assertRaisesRegex(RuntimeError, "preserving hard limit -1.*denied"):
                        lean_resources.configure_process_stack()

    def test_missing_resource_module_is_reported(self):
        with patch.object(lean_resources, "resource", None):
            record = lean_resources.configure_process_stack()
        self.assertFalse(record["supported"])
        self.assertFalse(record["changed"])
        self.assertIsNone(record["before"])
        self.assertIsNone(record["after"])
        self.assertIn("unavailable", record["reason"])

    def test_missing_stack_constant_is_reported(self):
        api = Mock(spec=[])
        with patch.object(lean_resources, "resource", api):
            record = lean_resources.configure_process_stack()
        self.assertFalse(record["supported"])


if __name__ == "__main__":
    unittest.main()
