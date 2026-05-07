# prismriver-live

Interactive Lean + music notebook for studying Ravel's Bolero with:
- Prismriver notation for musical structures
- Lean proofs for structural and mathematical properties
- VexFlow rendering in the browser

The main musical/proof example lives in [examples/bolero.lean](examples/bolero.lean).

## Quick Start

1. Serve the repository root:

```bash
python3 -m http.server 8765
```

2. Open:

http://localhost:8765/

3. The page loads [examples/bolero.lean](examples/bolero.lean) into the editor.

## Tutorial: Learn Prismriver and Lean Through Bolero

This tutorial shows how to model music in Prismriver and prove facts in Lean.

### 1. Prismriver: represent notes as data

In [examples/bolero.lean](examples/bolero.lean), we first import Prismriver and define a note type alias:

```lean
import Prismriver

open Prismriver.Classical

abbrev PNote := Prismriver.Classical.Note
```

Now we define musical phrases as lists of notes using Prismriver notation:

```lean
def ostinato : List PNote :=
	♩[c4 c4 c4 c4]

def themeA : List PNote :=
	♩[e4 f4 g4 a4 g4 f4 e4 d4]

def themeB : List PNote :=
	♩[c4 d4 e4 f4 e4 d4 c4 b4]
```

Key idea:
- Prismriver syntax builds ordinary Lean values.
- Once phrases are Lean values, we can compute and prove facts about them.

### 2. Lean: build form compositionally

Bolero is repetitive, so we model repetition with a function:

```lean
def repeatScore (n : Nat) (s : List PNote) : List PNote :=
	(List.replicate n s).foldr (· ++ ·) []
```

Then define the whole form:

```lean
def boleroScore : List PNote :=
	repeatScore 9 (repeatScore 16 ostinato ++ themeA ++ themeB)
```

Interpretation:
- Inner phrase: `repeatScore 16 ostinato ++ themeA ++ themeB`
- Outer form: repeat that phrase 9 times

### 3. Prove concrete musical facts

Lean can prove exact phrase lengths:

```lean
@[simp] theorem ostinato_length : ostinato.length = 4 := by native_decide
@[simp] theorem themeA_length   : themeA.length   = 8 := by native_decide
@[simp] theorem themeB_length   : themeB.length   = 8 := by native_decide
```

This says:
- Ostinato has 4 notes
- Theme A and Theme B each have 8 notes

### 4. Prove reusable algebra about repetition

These theorems let us reason about any repeated phrase:

```lean
theorem repeatScore_zero (s : List PNote) : repeatScore 0 s = [] := rfl
theorem repeatScore_one (s : List PNote) : repeatScore 1 s = s := by simp [repeatScore]

theorem repeatScore_length (n : Nat) (s : List PNote) :
		(repeatScore n s).length = n * s.length := by
	induction n with
	| zero => simp [repeatScore, Nat.zero_mul]
	| succ n ih =>
		show (s ++ repeatScore n s).length = (n + 1) * s.length
		rw [List.length_append, ih, Nat.succ_mul]; omega
```

What this gives you:
- A generic length law: repeating a phrase `n` times multiplies its length by `n`

### 5. Prove the full Bolero size

Now prove the whole form has 720 notes:

```lean
theorem boleroScore_length : boleroScore.length = 720 := by native_decide
```

This encodes:
- One cycle: `16 * 4 + 8 + 8 = 80`
- Full form: `9 * 80 = 720`

### 6. Model crescendo as an order property

The example also includes an abstract dynamics model:

```lean
def layer (i : Nat) : Nat := i
def dynamic (x : Nat) : Nat := x

theorem crescendo_monotonic : ∀ i, dynamic (layer i) < dynamic (layer (i + 1)) := by
	intro i; simp [layer, dynamic]
```

The meaning:
- Each later layer is louder than the previous one
- Crescendo becomes a theorem, not a comment

### 7. Check proof soundness

Use Lean's axiom audit:

```lean
#print axioms crescendo_monotonic
#print axioms repeatScore_length
#print axioms boleroScore_length
```

This helps verify no accidental `sorry`-based proofs are slipping in.

## How to Explore in the UI

In [index.html](index.html):
- Left panel: editable Lean source (loaded from [examples/bolero.lean](examples/bolero.lean))
- Right panel: rendered score for each `def ... : List PNote`
- Score navigation: windowed preview through long phrases
- Proof panel: live Lean diagnostics and axiom output

Tip:
- Select `boleroScore` and click Next in the score navigation to move through the form.

## Suggested Exercises

1. Add a new phrase `themeC : List PNote` and include it in `boleroScore`.
2. Prove `themeC.length = 8`.
3. Prove new total length after changing the form.
4. Replace `dynamic` with a custom step function and prove monotonicity.
5. Add a theorem relating bars to notes under 2/4 assumptions.

## Why this project is useful

Prismriver gives expressive musical notation.
Lean gives exact, machine-checked guarantees.
Together, they let you treat compositional form as both art and formal structure.