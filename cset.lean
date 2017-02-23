/- CUBICAL SETS -/
import .cubes
universes u v

/- Cubical Sets -/
structure cset {base : Type u} {fam : base → Type v} :=
    (obj        : base → Type)
    (mor        : Π {m n} (f : cmor (fam m) (fam n)), obj m → obj n)
    (cset_id    : Π {m} u, mor (cid (fam m)) u = u)
    (cset_comp  : Π {m n o : base} {f : cmor (fam m) (fam n)} {g : cmor (fam n) (fam o)} u,
         mor (ccomp g f) u = mor g (mor f u))

/- Some common instantiations of base and fam -/
check @cset.mk Type list
check @cset.mk ℕ fin
check @cset.mk unit (λ _, Type)

/- Maps between cubical sets -/
structure cset_mor {base : Type u} {fam : base → Type v} (X Y : @cset base fam) :=
    (trans  : Π m, X^.obj m → Y^.obj m)
    (nat    : Π {m n} (f : cmor (fam m) (fam n)), trans n ∘ X^.mor f = Y^.mor f ∘ trans m)

