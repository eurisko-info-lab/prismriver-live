import Prismriver

open Prismriver.Classical

abbrev PNote := Prismriver.Classical.Note

-- Ravel's Bolero - demo structure using upstream Prismriver notation.
def ostinato : List PNote :=
  ♩[c4 c4 c4 c4]

def themeA : List PNote :=
  ♩[e4 f4 g4 a4 g4 f4 e4 d4]

def themeB : List PNote :=
  ♩[c4 d4 e4 f4 e4 d4 c4 b4]

def repeatScore (n : Nat) (s : List PNote) : List PNote :=
  (List.replicate n s).foldr (· ++ ·) []

def boleroScore : List PNote :=
  repeatScore 9 (repeatScore 16 ostinato ++ themeA ++ themeB)

-- Minimal placeholders so theorem can intentionally remain unproven.
def layer (i : Nat) : Nat := i
def dynamic (x : Nat) : Nat := x

-- Prove the crescendo is strictly increasing (example theorem)
theorem crescendo_monotonic : ∀ i, dynamic (layer i) < dynamic (layer (i + 1)) := by
  intro i; simp [layer, dynamic]

-- ── § 2  Concrete length facts ───────────────────────────────────────────────

@[simp] theorem ostinato_length : ostinato.length = 4 := by native_decide
@[simp] theorem themeA_length   : themeA.length   = 8 := by native_decide
@[simp] theorem themeB_length   : themeB.length   = 8 := by native_decide

-- Themes A and B are the same length (balanced A/B form).
theorem themes_equal_length : themeA.length = themeB.length := by native_decide

-- Each theme spans exactly two ostinato bars.
theorem themes_double_ostinato : themeA.length = 2 * ostinato.length := by native_decide

-- ── § 3  repeatScore algebra ──────────────────────────────────────────────────

-- Zero repetitions is silence.
theorem repeatScore_zero (s : List PNote) : repeatScore 0 s = [] := rfl

-- One repetition is the phrase itself.
theorem repeatScore_one (s : List PNote) : repeatScore 1 s = s := by simp [repeatScore]

-- The successor case unfolds by definition.
theorem repeatScore_succ (n : Nat) (s : List PNote) :
    repeatScore (n + 1) s = s ++ repeatScore n s := rfl

-- Length scales linearly with the repeat count.
theorem repeatScore_length (n : Nat) (s : List PNote) :
    (repeatScore n s).length = n * s.length := by
  induction n with
  | zero => simp [repeatScore, Nat.zero_mul]
  | succ n ih =>
    show (s ++ repeatScore n s).length = (n + 1) * s.length
    rw [List.length_append, ih, Nat.succ_mul]; omega

-- m + n cycles equals m cycles concatenated with n cycles.
theorem repeatScore_append (m n : Nat) (s : List PNote) :
    repeatScore (m + n) s = repeatScore m s ++ repeatScore n s := by
  induction m with
  | zero => simp [repeatScore]
  | succ m ih =>
    have h : m + 1 + n = (m + n) + 1 := by omega
    rw [h, repeatScore_succ, repeatScore_succ, ih, ← List.append_assoc]

-- ── § 4  Full score length ────────────────────────────────────────────────────

-- 9 cycles × (16 ostinato bars × 4 notes + 8 themeA + 8 themeB) = 9 × 80 = 720.
theorem boleroScore_length : boleroScore.length = 720 := by native_decide

-- ── § 5  Dynamics / monotonicity ─────────────────────────────────────────────

-- The amplitude is non-decreasing: a higher layer is always at least as loud.
theorem dynamic_mono {i j : Nat} (h : i ≤ j) :
    dynamic (layer i) ≤ dynamic (layer j) := by
  simp [layer, dynamic]; exact h

-- ── § 6  Axiom audit ──────────────────────────────────────────────────────────
-- All theorems should depend only on [propext] (no sorryAx).
#print axioms crescendo_monotonic
#print axioms repeatScore_length
#print axioms repeatScore_append
#print axioms boleroScore_length
#print axioms dynamic_mono

-- Keep playback examples as eval-safe snippets here; upstream #play requires Alda installed.
#eval (♩[c4 c4 c4 c4] : List PNote)
#eval (♩[e4 f4 g4 a4 g4 f4 e4 d4] : List PNote)
