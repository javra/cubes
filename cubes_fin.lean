/- THE CUBE CATEGORY ON FINITE SETS -/
import .cubes

open cmonad fin nat

universes u v

def cfin (n : ℕ) := cmonad (fin n)

/- Projecting at the i-th dimension -/
-- TODO generalize this to arbitrary elementary surjections?
def cproj : Π {m}, bool → fin (m + 1) → cmor (fin (m + 1)) (fin m)
| 0       b _                 _                 := b
| (m + 1) b (mk 0 _)          (mk 0 _)          := b
| (m + 1) b (mk 0 _)          (mk (l + 1) l_lt) := dim $ mk l (lt_of_succ_lt_succ l_lt)
| (m + 1) b (mk (i + 1) i_lt) (mk 0 z_lt)       := dim $ mk 0 (zero_lt_succ _)
| (m + 1) b (mk (i + 1) i_lt) (mk (l + 1) l_lt) := 
    do (mk x x_lt) <- cproj b (mk i (lt_of_succ_lt_succ i_lt)) (mk l (lt_of_succ_lt_succ l_lt)),
       return (mk (x + 1) (succ_lt_succ x_lt))

/- Degenerating at the i-th dimenion -/
def cdeg : Π {m}, fin (m + 1) → cmor (fin m) (fin (m + 1))
| m       (mk 0 _)          (mk l l_lt)       := dim $ mk (l + 1) (succ_lt_succ l_lt)
| m       (mk (i + 1) _)    (mk 0 _)          := dim $ mk 0 (zero_lt_succ _)
| 0       _                 (mk l l_lt)       := dim $ mk (l + 1) (succ_lt_succ l_lt)
| (m + 1) (mk (i + 1) i_lt) (mk (l + 1) l_lt) :=
    do (mk x x_lt) <- @cdeg _ (mk i (lt_of_succ_lt_succ i_lt)) (mk l (lt_of_succ_lt_succ l_lt)),
       return (mk (x + 1) (succ_lt_succ x_lt))

set_option pp.implicit true
theorem cproj_of_cdeg {m} {b : bool} (k : fin (m + 1)) : cproj b k ∘c cdeg k = cid _ :=
begin
  apply funext, intros, cases x with x x_lt, --simp[cid,ccomp,cdeg],
  induction m with m IHm,
  { cases k with k k_lt, induction k with k IHk, apply absurd x_lt, apply not_lt_zero,
    simp[cid], apply absurd (lt_of_succ_lt_succ k_lt), apply not_lt_zero },
  { cases k with k k_lt, induction k with k IHk, 
    { cases x, reflexivity, reflexivity },
    { cases x with x x_lt, reflexivity, simp[cid, cproj, cdeg], unfold cdeg, } }
    
end

--def cproj_succ_comm {m} {b c : bool} (k : fin (m + 2))