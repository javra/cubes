/- THE CUBE CATEGORY ON fiITE SETS -/
import .cubes
import .fi

open cmonad fi nat

universes u v

def cfi (n : ℕ) := cmonad (fi n)

/- Projecting at the i-th dimension -/
-- TODO generalize this to arbitrary elementary surjections?
def cproj (b : bool) : Π {m}, fi (m + 1) → cmor (fi (m + 1)) (fi m)
| m       fi.zero fi.zero := b
| (m + 1) fi.zero (suc j) := dim j
| (m + 1) (suc i) fi.zero := dim fi.zero
| (m + 1) (suc i) (suc j) := do x <- cproj i j,
                                return $ suc x

def cdeg {m} (i : fi (m + 1)) : cmor (fi m) (fi (m + 1)) := dim ∘ deg i

theorem cproj_cdeg {m} {b : bool} (i : fi (m + 1)) : cproj b i ∘c cdeg i = dim :=
begin
  apply funext, intro j, change (_ ∘c dim) _ = _, rw cid_right,
  cases i with n n i,
  { induction j, reflexivity, reflexivity },
  { induction j with n n j ih_j, reflexivity, 
    simp[deg, cproj], cases i, 
    { cases j, reflexivity, reflexivity },
    { rw ih_j, reflexivity } }
end

def clift {n k} : Π m (f : cmor (fi n) (fi k)), cmor (fi (n + m)) (fi (k + m)) :=
begin
  intros m f i,
  induction m with m ih_m, exact f i,
  cases i with n n i, exact dim fi.zero,
  exact ((ih_m i) >>= (λ x, (return $ suc x)))
end

theorem clift_foo : clift 5 (@dim (fi 3)) = dim :=
begin
  apply funext, intro x, simp[clift], delta id_locked,
end

theorem clift_dim {m n : ℕ} : clift m (@dim (fi n)) = dim :=
begin
  induction m with m ih_m, reflexivity,
  apply funext, intro i, cases i with n n i, reflexivity,
  
end