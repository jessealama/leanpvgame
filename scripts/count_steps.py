#!/usr/bin/env python3
"""Count reference-proof tactic steps in lean4game level files.

Prints an informational report to stdout.
Exits 0 on success, 1 if any level file cannot be parsed.

A "step" is any non-blank, non-comment, non-Hint line inside the
  Statement ... := by
  ...
  Conclusion "..."
block.  Hint "..." strings are skipped in their entirety, including
multi-line hints.
"""

import re
import sys
from pathlib import Path


def count_steps(path: Path) -> int | None:
    """Return tactic step count for a level file, or None if no Statement found.

    Raises ValueError on structural parse errors.
    """
    lines = path.read_text(encoding="utf-8").splitlines()

    # ── Step 1: find proof_start (line after "Statement ... := by") ──────────
    proof_start: int | None = None
    in_stmt = False
    for i, line in enumerate(lines):
        s = line.strip()
        if not in_stmt and s.startswith("Statement "):
            in_stmt = True
        if in_stmt and s.endswith(":= by"):
            proof_start = i + 1
            break

    if proof_start is None:
        return None  # world file or stub with no proof

    # ── Step 2: find proof_end ("Conclusion" always at column 0) ─────────────
    proof_end: int | None = None
    for i in range(proof_start, len(lines)):
        if re.match(r"^Conclusion\b", lines[i]):
            proof_end = i
            break

    if proof_end is None:
        raise ValueError(f"{path}: no Conclusion found after Statement")

    # ── Step 3: walk proof lines, skipping blanks, comments, Hint blocks ─────
    steps = 0
    i = proof_start
    while i < proof_end:
        line = lines[i]
        s = line.strip()

        # blank or comment
        if not s or s.startswith("--"):
            i += 1
            continue

        # Hint block: skip from opening " to closing "
        # Handles: Hint "...", Hint (hidden := true) "...", multi-line hints.
        # Assumption: hint strings never contain an unescaped " character
        # (all inline code in our levels uses backticks).
        if re.match(r"Hint\b", s):
            chunk = "\n".join(lines[i:proof_end])
            open_q = chunk.find('"')
            if open_q == -1:
                i += 1
                continue
            close_q = chunk.find('"', open_q + 1)
            if close_q == -1:
                raise ValueError(
                    f"{path}:{i + 1}: unclosed Hint string"
                )
            # count newlines in chunk up to and including the closing-quote line
            lines_consumed = chunk[: close_q + 1].count("\n") + 1
            i += lines_consumed
            continue

        steps += 1
        i += 1

    return steps


def main() -> None:
    script_dir = Path(__file__).parent
    game_root = script_dir.parent
    levels_dir = game_root / "Game" / "Levels"

    if not levels_dir.is_dir():
        print(f"error: {levels_dir} not found", file=sys.stderr)
        sys.exit(1)

    # All L##_*.lean files, sorted by path
    level_files = sorted(levels_dir.rglob("L[0-9][0-9]_*.lean"))
    if not level_files:
        print("No level files found.")
        return

    rows: list[tuple[str, int]] = []
    errors: list[str] = []

    for path in level_files:
        rel = str(path.relative_to(levels_dir).with_suffix(""))
        try:
            n = count_steps(path)
            if n is not None:
                rows.append((rel, n))
        except ValueError as exc:
            errors.append(str(exc))

    if errors:
        for e in errors:
            print(f"parse error: {e}", file=sys.stderr)
        sys.exit(1)

    if not rows:
        print("No levels with proofs found.")
        return

    # ── Print table ───────────────────────────────────────────────────────────
    name_w = max(len(name) for name, _ in rows)
    name_w = max(name_w, 20)

    header = f"{'Level':<{name_w}}  {'Steps':>5}  Chart"
    print("=== Proof Step Report ===")
    print(header)
    print("-" * len(header))

    max_steps = max(n for _, n in rows)
    bar_scale = 20 / max(max_steps, 1)  # bars top out at 20 chars

    for name, n in rows:
        bar = "█" * round(n * bar_scale)
        print(f"{name:<{name_w}}  {n:5d}  {bar}")

    print("-" * len(header))
    avg = sum(n for _, n in rows) / len(rows)
    max_name = next(name for name, n in rows if n == max_steps)
    print(
        f"{'Levels: ' + str(len(rows)):<{name_w}}"
        f"  avg {avg:.1f}"
        f"  max {max_steps} ({max_name})"
    )


if __name__ == "__main__":
    main()
