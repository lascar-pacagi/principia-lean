"""Reset listed exercise bodies, preserving statements and supplied code."""

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import re
import shutil


def mask_comments_and_strings(source):
    """Keep character positions and newlines while hiding Lean comments/strings."""
    result = list(source)
    i = 0
    while i < len(source):
        start = i
        if source.startswith("--", i):
            i = source.find("\n", i)
            if i < 0:
                i = len(source)
        elif source.startswith("/-", i):
            depth = 1
            i += 2
            while i < len(source) and depth:
                if source.startswith("/-", i):
                    depth += 1
                    i += 2
                elif source.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError("Unclosed block comment")
        elif source[i] == '"':
            i += 1
            while i < len(source):
                if source[i] == "\\":
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            else:
                raise ValueError("Unclosed string")
            # Keep a nonblank token so a string-only body isn't mistaken for empty.
            for j in range(start, min(i, len(source))):
                if source[j] != "\n":
                    result[j] = "x"
            continue
        else:
            i += 1
            continue
        for j in range(start, i):
            if source[j] != "\n":
                result[j] = " "
    return "".join(result)


DECLARATION = re.compile(
    r"(?m)^(?P<indent>[^\S\n]*)(?:@\[[^\n]*\]\s*)?"
    r"(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    r"(?:theorem|lemma|def)\s+(?P<name>[^\s(:]+)"
)


def reset_source(source, exercise_names):
    clean = mask_comments_and_strings(source)
    edits = []
    found = set()
    for declaration in DECLARATION.finditer(clean):
        name = declaration["name"]
        if name not in exercise_names:
            continue
        if name in found:
            raise ValueError(f"Ambiguous exercise declaration: {name}")
        found.add(name)
        indent = declaration["indent"]
        # Skeleton declarations use a command at the same indentation to end a body.
        boundary = re.compile(
            r"(?m)^" + re.escape(indent)
            + r"(?=\S)(?!(?:where|termination_by|decreasing_by)\b)"
        ).search(clean, declaration.end())
        end = boundary.start() if boundary else len(clean)
        depth = 0
        assignment = None
        for i in range(declaration.end(), end):
            if clean[i] in "([{⟨":
                depth += 1
            elif clean[i] in ")]}⟩":
                depth -= 1
            elif depth == 0 and clean.startswith(":=", i):
                assignment = i + 2
                break
        if assignment is None:
            raise ValueError(f"No := body found for exercise: {name}")
        body_end = assignment + len(clean[assignment:end].rstrip())
        if body_end == assignment:
            raise ValueError(f"Empty proof body for exercise: {name}")
        edits.append((assignment, body_end, f" by\n{indent}  sorry"))
    missing = set(exercise_names) - found
    if missing:
        raise ValueError("Missing exercises: " + ", ".join(sorted(missing)))
    for start, end, replacement in reversed(edits):
        source = source[:start] + replacement + source[end:]
    return source


def reset_course(root, concept=None, dry_run=False):
    root = Path(root).resolve()
    manifest = json.loads((root / "tooling/exercises.json").read_text())
    if concept:
        selected = (root / concept).resolve()
        if not selected.is_relative_to(root) or selected == root:
            raise ValueError("C must name a concept directory inside course/")
        manifest = {name: goals for name, goals in manifest.items()
                    if (root / name).is_relative_to(selected)}
        if not manifest:
            raise ValueError(f"No registered exercises in {concept}")
    changes = []
    # Validate every selected file before modifying any of them.
    for name, goals in manifest.items():
        path = root / name
        if path.is_symlink() or not path.resolve().is_relative_to(root):
            raise ValueError(f"Exercise file must be inside course/: {name}")
        source = path.read_text()
        try:
            replacement = reset_source(source, goals)
        except ValueError as error:
            raise ValueError(f"{name}: {error}") from error
        if replacement != source:
            changes.append((path, replacement))
    if not changes:
        print("All selected exercises already have empty proof bodies.")
        return None
    for path, _ in changes:
        print(f"{'Would reset' if dry_run else 'Reset'} {path.relative_to(root)}")
    if dry_run:
        print(f"Preview: {len(changes)} files; no files changed.")
        return None
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    backup = root / ".exercise-backups" / stamp
    for path, _ in changes:
        destination = backup / path.relative_to(root)
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(path, destination)
    for path, replacement in changes:
        path.write_text(replacement)
    print(f"Reset {len(changes)} files. Previous answers saved in {backup}")
    return backup


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--concept", help="Reset just this concept, including optional exercises")
    parser.add_argument("--dry-run", action="store_true", help="Preview without modifying files")
    args = parser.parse_args()
    try:
        reset_course(Path(__file__).resolve().parent.parent, args.concept, args.dry_run)
    except (ValueError, OSError) as error:
        parser.exit(1, f"Reset failed: {error}\n")


if __name__ == "__main__":
    main()
