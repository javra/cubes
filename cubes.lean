/- THE CUBE CATEGORY -/

universes v u

inductive cmonad (α : Type u)   | ll {}  : cmonad
                                | rr {}  : cmonad
                                | dim {} : α → cmonad
open cmonad

def bool_to_cmonad {α : Type u} : bool → cmonad α
| ff := ll
| tt := rr

instance inst_bool_to_cmonad (α : Type u) : has_coe bool (cmonad α) :=
⟨ bool_to_cmonad ⟩

@[inline] def cmor (α β) := α → cmonad β

@[inline] def cbind {α : Type u} {β : Type v} (x) (f : cmor α β) : cmonad β :=
match x with
| ll    := ll
| rr    := rr
| dim x := f x
end

def cmap {α : Type u} {β : Type v} (f : α → β) (x : cmonad α) : cmonad β :=
match x with
| ll    := ll
| rr    := rr
| dim x := dim (f x)
end

instance inst_cmonad : monad cmonad :=
{ map := @cmap, bind := @cbind, ret := @dim }

theorem cbind_bool {α β : Type u} (b : bool) (f : cmor α β) : (↑b >>= f) = ↑b :=
by cases b; reflexivity; reflexivity; reflexivity

theorem cbind_dim {α β : Type u} (a : α) (f : cmor α β) : (dim a >>= f) = f a :=
rfl

theorem cbind_assoc {α β γ : Type u} (a : cmonad α) (f : cmor α β) (g : cmor β γ) :
  ((a >>= f) >>= g) = (a >>= (λ x, f x >>= g)) :=
sorry

/- The identity cube map is just return is just dim -/

/- Composition of cube maps -/
def ccomp {α β γ} (g : cmor β γ) (f : cmor α β) : cmor α γ :=
λ x, do y <- f x,
        g y

infixl ` ∘c `:90 := ccomp

/- The monad laws for cmonad -/
theorem cid_left {α β} (f : cmor α β) (x : α) : (dim ∘c f) x = f x :=
begin
  simp[ccomp],
  exact  match (f x) with
         | ll    := rfl
         | rr    := rfl
         | dim a := rfl
         end
end

theorem cid_right {α β} (f : cmor α β) (x : α) : (f ∘c dim) x = f x :=
begin
  simp[ccomp],
  exact rfl
end

theorem ccomp_assoc {α β γ δ} (f : cmor α β) (g : cmor β γ) (h : cmor γ δ) (x) :
    ((h ∘c g) ∘c f) x = (h ∘c (g ∘c f)) x :=
begin
  simp[ccomp],
  exact match (f x) with
        | ll    := rfl
        | rr    := rfl
        | dim x := rfl
        end
end

/- TODO Instantiate cmonad as internal category -/

def is_strict {α β} (f : cmor α β) : Prop := ∀ a, ∃ x, f a = dim x
