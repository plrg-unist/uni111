def sqrt (n : Nat) : Nat :=
  let rec loop (r fuel : Nat) : Nat :=
    match fuel with
    | 0 => r
    | fuel' + 1 =>
      if (r + 1) * (r + 1) ≤ n then
        loop (r + 1) fuel'
      else
        r
  loop 0 n

theorem sqrt_bounds {n r : Nat} (h : sqrt n = r) :
    r * r ≤ n ∧ n < (r + 1) * (r + 1) := by
  sorry

def sqrtFast (n : Nat) : Nat :=
  if n < 2 then
    n
  else
    let r := 2 * sqrtFast (n / 4)
    if (r + 1) * (r + 1) ≤ n then
      r + 1
    else
      r

theorem sqrtFast_bounds {n r : Nat} (h : sqrtFast n = r) :
    r * r ≤ n ∧ n < (r + 1) * (r + 1) := by
  sorry
