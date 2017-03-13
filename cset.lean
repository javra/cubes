/- CUBICAL SETS -/
import .cubes
import .fi
import .cubes_fin
universes u v

open cmonad

/- Cubical Sets -/
structure cset {base : Type u} {fam : base → Type v} :=
    (obj        : base → Type)
    (mor        : Π {m n} (f : cmor (fam m) (fam n)), obj m → obj n)
    (id    : Π {m} u, mor (@dim (fam m)) u = u)
    (comp  : Π {m n o : base} {f : cmor (fam m) (fam n)} {g : cmor (fam n) (fam o)} u,
         mor (g ∘c f) u = mor g (mor f u))

/- Some common instantiations of base and fam -/
/-check @cset.mk Type list
check @cset.mk ℕ fin
check @cset.mk unit (λ _, Type)-/

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

def fcset := @cset ℕ fi

/- The path cubical set. The "new" dimension is represented by fi.zero -/
section fcset
variables (X : fcset)

def path_cset : fcset :=
{cset . obj := λ m, X^.obj (m + 1),
        mor := λ m n f u, X^.mor (clift f) u,
        id := λ m u, by rw clift_dim; apply X^.id,
        comp := λ m n o f g u, by rw clift_ccomp; apply X^.comp }

def proj {m} (u : X^.obj (m + 1)) (b : bool) := X^.mor (cproj b (@fi.zero m)) u

/- The homogeneous idenity cubical set without Kan property -/
/- This kind of corresponds to the set of paths from δ ff to δ tt -/
-- TODO make fcset a substructure to cset
-- TODO define sub-cubical sets
def id_cset (δ : bool → X^.obj 0) : fcset :=
{cset . obj := λ m, subtype (λ (w : X^.obj (m + 1)), ∀ b, proj X w b = (X^.mor zero_deg) (δ b)),
        mor := λ m n f u, begin
                        cases u with u hu, existsi X^.mor (clift f) u,
                        intro b, simp[proj], rw -X^.comp,
                        rw [cproj_clift, X^.comp], delta proj at hu,
                        rw [hu, -X^.comp, zero_deg_right],
                end,
        id := λ m u, begin
                        cases u with u hu, apply subtype.eq,
                        simp, rw [clift_dim, X^.id],
                end,
        comp := λ m n o f g u, begin
                        cases u with u hu, apply subtype.eq, simp,
                        rw [clift_ccomp, X^.comp]
                end}

def prod_cset (X Y : fcset)  : fcset :=
{cset . obj := λ m, X^.obj m × Y^.obj m, 
        mor := λ m n f u, ⟨ X^.mor f u.1, Y^.mor f u.2 ⟩,
        id := λ m u, by cases u; rw [X^.id, Y^.id],
        comp := λ m n o f g u, by cases u; rw[X^.comp, Y^.comp] }

end fcset

