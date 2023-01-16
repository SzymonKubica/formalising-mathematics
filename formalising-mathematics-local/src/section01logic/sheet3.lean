/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes:
https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2023/Part_B/equality.html

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

-- Random code from lectures

def D : Prop := 2 + 2 = 5

#check D
#print D

variables (P Q R : Prop)

example : ¬ true → false :=
begin
  by_contra,
end

example : false → ¬ true :=
begin
  sorry
end

example : ¬ false → true :=
begin
  sorry
end

example : true → ¬ false :=
begin
  sorry
end

example : false → ¬ P :=
begin
  sorry
end

example : P → ¬ P → false :=
begin
  sorry
end

example : P → ¬ (¬ P) :=
begin
  sorry
end

example : (P → Q) → (¬ Q → ¬ P) :=
begin
  sorry
end

example : ¬ ¬ false → false :=
begin
  sorry
end

example : ¬ ¬ P → P :=
begin
  sorry
end

example : (¬ Q → ¬ P) → (P → Q) :=
begin
  sorry,
end
