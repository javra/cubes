/- THE CUBE CATEGORY -/

universes v u

inductive cm (α : Type u)   | ll {}  : cm
                            | rr {}  : cm
                            | dim {} : α → cm
open cm

def cbind {α : Type u} {β : Type v} (x : cm α) (f : α → cm β) : cm β :=
match x with
| ll    := ll
| rr    := rr
| dim x := f x
end

def cmap {α : Type u} {β : Type v} (f : α → β) (x : cm α) : cm β :=
match x with
| ll    := ll
| rr    := rr
| dim x := dim (f x)
end

def cret {α : Type u} (a : α) : cm α := dim a

instance cmonad : monad cm :=
{ map := @cmap, bind := @cbind, ret := @cret }

@[inline] def cmor (α β) := α → cm β

/- Identity cube map -/
def cid (α) : cmor α α := return

/- Composition of cube maps -/
def ccomp {α β γ} (g : cmor β γ) (f : cmor α β) : cmor α γ :=
λ x, do y <- f x,
        g y

infixl ` ∘c `:90 := ccomp

def cid_left {α β} (f : cmor α β) : (cid β) ∘c f = f :=
sorry -- FOLLOWS FROM MONAD LAWS!

def is_strict {α β} (f : cmor α β) : Prop := ∀ a, ∃ x, f a = dim x
