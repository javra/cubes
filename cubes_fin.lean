/- THE CUBE CATEGORY ON fiITE SETS -/
import .cubes .fi

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
                                dim $ suc x

--TODO simplify this
theorem cproj_self (b : bool) {m} (i : fi (m + 1)) : cproj b i i = b :=
begin
  cases i with n n i,
  { cases m, repeat {reflexivity} },
  { induction i with n n i ih_i, simp[cproj], 
    { cases n, repeat {simp[cproj], rw cbind_bool} },
    { simp[cproj], rw [ih_i, cbind_bool] } }
end

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

/- Lift a cubical morphism by 1 -/
-- TODO generalize this
def clift {n k} (f : cmor (fi n) (fi k)) : cmor (fi (succ n)) (fi (succ k))
| fi.zero := dim fi.zero
| (suc i) := do x <- f i,
                dim $ suc x

theorem clift_suc {n k} (f : cmor (fi n) (fi k)) (i : fi n) :
    clift f (suc i) = (f i >>= (dim ∘ suc)) :=
by reflexivity

theorem clift_dim {n : ℕ} : clift (@dim (fi n)) = dim :=
begin
  apply funext, intro i, cases i, repeat {reflexivity},
end

theorem clift_ccomp {m n o : ℕ} (f : cmor (fi m) (fi n)) (g : cmor (fi n) (fi o)) :
  clift (g ∘c f) = (clift g) ∘c (clift f) :=
begin
  apply funext, intro i, cases i with n n i, reflexivity,
  simp[clift,ccomp], cases (f i) with j, reflexivity, reflexivity,
  change (g j >>= _) = clift _ _, rw clift_suc,
end

--TODO generalize to arbitrary projections
theorem cproj_clift {m n : ℕ} (f : cmor (fi m) (fi n)) (b : bool) :
  (cproj b fi.zero) ∘c (clift f) = f ∘c (cproj b fi.zero) :=
begin
  apply funext, intro i, cases i with n n i,
  simp[ccomp, clift], rw [cproj_self, cbind_bool, cbind_dim, cproj_self],
  { cases m, simp[ccomp], cases i,
    simp[ccomp, cproj, clift], rw [cbind_dim, cbind_assoc], 
    cases f i with j, reflexivity, reflexivity, rw cbind_dim, rw cbind_dim, 
    cases n, cases j, reflexivity }
end

def zero_deg {m : ℕ} : cmor (fi 0) (fi m) := λ i, match i with
                                                  end

theorem zero_deg_right {m n : ℕ} (f : cmor (fi m) (fi n)) :
  f ∘c zero_deg = zero_deg :=
begin
  apply funext, intro i, cases i
end