/- CUBICAL SETS -/
import .cubes
universes u v

/- Cubical Sets -/
structure cset {base : Type u} {fam : base → Type v} :=
    (obj        : base → Type)
    (mor        : Π {m n} (f : cmor (fam m) (fam n)), obj m → obj n)
    (id    : Π {m} u, mor (cid (fam m)) u = u)
    (comp  : Π {m n o : base} {f : cmor (fam m) (fam n)} {g : cmor (fam n) (fam o)} u,
         mor (ccomp g f) u = mor g (mor f u))

/- Some common instantiations of base and fam -/
check @cset.mk Type list
check @cset.mk ℕ fin
check @cset.mk unit (λ _, Type)

/- Maps between cubical sets -/
structure cset_mor {base : Type u} {fam : base → Type v} (X Y : @cset base fam) :=
    (trans  : Π m, X^.obj m → Y^.obj m)
    (nat    : Π {m n} (f : cmor (fam m) (fam n)), trans n ∘ X^.mor f = Y^.mor f ∘ trans m)

/- The constant (or discrete) cubical set -/
def const_cset {base : Type u} (α : Type) : @cset base (λ i, Type (u+1)) :=
{cset . obj := λ m, α,
        mor := λ m n f u, u,
        id := λ m u, rfl, 
        comp := λ m n o f g u, rfl }
 
 /- Representable (yoneda) cubical sets -/
def rep_cset {base : Type u} {fam : base → Type} (k : base) :=
{cset . obj := λ n, cmor (fam k) (fam n),
        mor := λ m n f u, f ∘c u,
        id := λ m u, begin apply funext, intro x, apply cid_left end,
        comp := λ m n o f g u, begin apply funext, intro x, apply ccomp_assoc end }