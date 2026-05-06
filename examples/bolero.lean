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

-- This explicitly reports unresolved axioms (including sorryAx).
#print axioms crescendo_monotonic

-- Keep playback examples as eval-safe snippets here; upstream #play requires Alda installed.
#eval (♩[c4 c4 c4 c4] : List PNote)
#eval (♩[e4 f4 g4 a4 g4 f4 e4 d4] : List PNote)
