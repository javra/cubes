/- THE UNIFORM KAN CONDITION ON CUBICAL SETS -/
import .cset

structure open_box (X : fcset) (m : ℕ) (a : bool) (S : set (fi $ m + 1)) :=
  (bottom : X^.obj (m + 1))
  (side : Π (i ∈ S) (b : bool), X^.obj (m + 1))
  (adj_bottom : Π (i ∈ S) (b : bool), 
    X^.zproj a (side i H b) = X^.proj i b bottom)
  (adj_side : Π {i} (Hi: i ∈ S) {j} (Hj: j ∈ S) (b c : bool),
    X^.proj j b (side i Hi c) = X^.proj i c (side j Hj c)) 

