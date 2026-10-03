namespace Jsp000616

-- A set is sum-free if no a,b in the set have a+b also in the set
-- For {1,2,...,n}, the number of sum-free subsets is known
-- Let's verify small cases by explicit enumeration

-- Define: is S sum-free (as a list of nats)
def IsSumFree : List Nat → Bool
  | [] => true
  | (x :: xs) => 
    -- x+x not in xs, and for each y in xs: x+y not in x::xs
    let check_y : List Nat → Bool := fun ys => ys.all (fun y => 
      (x + y) ∉ (x :: xs))
    (x + x ∉ xs) ∧ check_y xs ∧ IsSumFree xs

-- Known: number of sum-free subsets of {1,2,...,n} for small n
-- n=0: 1 (empty set)
-- n=1: 2 (∅, {1}) — both sum-free
-- n=2: 3 (∅, {1}, {2}) — {1,2}: 1+1=2 ∈ {1,2} so NOT sum-free
-- n=3: 6 (∅, {1}, {2}, {3}, {2,3}, {1,3}) — check {1,2}: 1+1=2 ∈ set ✗
-- n=4: 8 — need to verify

-- Let's just verify n=3 explicitly
theorem n3_sumfree :
    IsSumFree [] = true ∧
    IsSumFree [1] = true ∧
    IsSumFree [2] = true ∧
    IsSumFree [3] = true ∧
    IsSumFree [2,3] = true ∧
    IsSumFree [1,3] = true ∧
    IsSumFree [1,2] = false := by decide

end Jsp000616