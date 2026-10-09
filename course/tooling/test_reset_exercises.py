import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest

from reset_exercises import reset_course, reset_source


class ResetTests(unittest.TestCase):
    def test_preserves_statements_supplied_code_and_nested_comments(self):
        source = '''namespace Practice
/- A comment with theorem fake := by
   /- Nested comment -/
-/
def given : String := "theorem fake := sorry"
@[simp] theorem goal
    (n : Nat) : n + 0 = n := by
  have helper : n = n := by
    rfl
  exact rfl

end Practice
'''
        expected = source.replace(''' by
  have helper : n = n := by
    rfl
  exact rfl''', ''' by
  sorry''')
        self.assertEqual(reset_source(source, ["goal"]), expected)

    def test_resets_definition_without_resetting_helpers(self):
        source = '''def helper (n : Nat) := n + 1
def exercise (n : Nat) : Nat :=
  helper n
def other (n : Nat) := exercise n
'''
        self.assertEqual(
            reset_source(source, ["exercise"]),
            source.replace('''
  helper n''', ''' by
  sorry'''),
        )

    def test_ignores_assignment_inside_parameter_default(self):
        source = 'theorem goal (n : Nat := 0) : n = n := by rfl\n'
        self.assertEqual(
            reset_source(source, ["goal"]),
            'theorem goal (n : Nat := 0) : n = n := by\n  sorry\n',
        )

    def test_string_body_and_idempotence(self):
        source = 'def exercise : String := "hello"\n'
        reset = reset_source(source, ["exercise"])
        self.assertEqual(reset, 'def exercise : String := by\n  sorry\n')
        self.assertEqual(reset_source(reset, ["exercise"]), reset)

    def make_course(self, root):
        manifest = {
            "lesson/Skeleton.lean": ["goal"],
            "lesson/optional/Skeleton.lean": ["goal"],
            "other/Skeleton.lean": ["goal"],
        }
        (root / "tooling").mkdir()
        (root / "tooling/exercises.json").write_text(json.dumps(manifest))
        for name in manifest:
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('theorem goal : True := by trivial\n')
            path.with_name("Solution.lean").write_text('theorem goal : True := by trivial\n')

    def test_preview_backup_scoping_and_idempotence(self):
        with tempfile.TemporaryDirectory() as directory, contextlib.redirect_stdout(io.StringIO()):
            root = Path(directory)
            self.make_course(root)
            originals = {p: p.read_bytes() for p in root.rglob("*.lean")}
            reset_course(root, "lesson", dry_run=True)
            self.assertFalse((root / ".exercise-backups").exists())
            self.assertTrue(all(p.read_bytes() == text for p, text in originals.items()))
            backup = reset_course(root, "lesson")
            self.assertIsNotNone(backup)
            for path, text in originals.items():
                if path.name == "Skeleton.lean" and "lesson" in path.parts:
                    self.assertIn("sorry", path.read_text())
                    self.assertEqual((backup / path.relative_to(root)).read_bytes(), text)
                else:
                    self.assertEqual(path.read_bytes(), text)
            self.assertIsNone(reset_course(root, "lesson"))
            self.assertEqual(len(list((root / ".exercise-backups").iterdir())), 1)

    def test_invalid_input_does_not_partially_reset(self):
        with tempfile.TemporaryDirectory() as directory, contextlib.redirect_stdout(io.StringIO()):
            root = Path(directory)
            self.make_course(root)
            (root / "other/Skeleton.lean").write_text("-- missing exercise\n")
            originals = {p: p.read_bytes() for p in root.rglob("*.lean")}
            with self.assertRaisesRegex(ValueError, "Missing exercises"):
                reset_course(root)
            self.assertTrue(all(p.read_bytes() == text for p, text in originals.items()))
            self.assertFalse((root / ".exercise-backups").exists())
            with self.assertRaises(ValueError):
                reset_course(root, "../elsewhere")

    def test_all_course_skeletons_reset_on_copy(self):
        course = Path(__file__).resolve().parent.parent
        manifest_path = course / "tooling/exercises.json"
        manifest = json.loads(manifest_path.read_text())
        with tempfile.TemporaryDirectory() as directory, contextlib.redirect_stdout(io.StringIO()):
            root = Path(directory)
            (root / "tooling").mkdir()
            (root / "tooling/exercises.json").write_bytes(manifest_path.read_bytes())
            for name in manifest:
                destination = root / name
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes((course / name).read_bytes())
            reset_course(root)
            for name, goals in manifest.items():
                source = (root / name).read_text()
                self.assertEqual(source, reset_source(source, goals), name)
            self.assertIsNone(reset_course(root))


if __name__ == "__main__":
    unittest.main()
