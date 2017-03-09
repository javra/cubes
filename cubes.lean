/- THE CUBE CATEGORY -/

universes v u

inductive cmonad (α : Type u)   | ll {}  : cmonad
                                | rr {}  : cmonad
                                | dim {} : α → cmonad
open cmonad

instance bool_to_cmonad (α : Type u) : has_coe bool (cmonad α) :=
⟨λ b, match b with ff := ll
                              | tt := rr
                   end⟩

@[inline] def cbind {α : Type u} {β : Type v} (x) (f : α → cmonad β) : cmonad β :=
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

@[inline] def cmor (α β) := α → cmonad β

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
