import tactic

variable (n : ℕ)

def f : ℤ -> ℤ := λ n, n^2

example (n : ℕ) : false :=
begin
 let z : ℤ := f n,
 sorry,
end

-- Up arrow with the bottom line is a function which takes terms and promotes them
-- to types.

-- Double up arrow is a function from terms to functions. it is called coe_fun.

-- Integers are defined in a weird way

