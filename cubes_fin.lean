/- THE CUBE CATEGORY ON FINITE SETS -/
import .cubes

open cmonad fin nat

universes u v

def cfin (n : ℕ) := cmonad (fin n)

-- TODO generalize this to arbitrary elementary surjections?
def cproj : Π {m}, bool → fin (m+1) → cmor (fin (m+1)) (fin m)
| 0       ff _        _                         := ll
| 0       tt _        _                         := rr
| (m + 1) ff (mk 0 _) (mk 0 _)                  := ll
| (m + 1) tt (mk 0 _) (mk 0 _)                  := rr
| (m + 1) b (mk 0 _) (mk (l + 1) l_lt)          := dim (mk l (lt_of_succ_lt_succ l_lt))
| (m + 1) b (mk (n + 1) n_lt) (mk 0 z_lt)       := dim (mk 0 (zero_lt_succ _))
| (m + 1) b (mk (n + 1) n_lt) (mk (l + 1) l_lt) := 
    do (mk x x_lt) <- @cproj m b (mk n (lt_of_succ_lt_succ n_lt)) (mk l (lt_of_succ_lt_succ l_lt)),
       return (mk x (lt_trans x_lt (self_lt_succ m)))