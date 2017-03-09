inductive fi : ℕ → Type 
| zero : Π {n}, fi (n + 1)
| suc : Π {n}, fi n → fi (n + 1)
open fi

namespace fi

instance {n : ℕ} : has_zero (fi (n + 1)) := ⟨ fi.zero ⟩

def fi_to_nat : Π {n}, fi n → ℕ
| (n + 1) fi.zero := nat.zero
| (n + 1) (suc i) := nat.succ (fi_to_nat i)

instance fi_nat_coe {n : ℕ} : has_coe (fi n) ℕ := ⟨ fi_to_nat ⟩

def raise {m} : Π n, fi m → fi (m + n)
| 0       i := i
| (n + 1) i := fi.suc (raise n i)

-- TODO: Instantiate as numeral

def inject : Π {n}, fi n → fi (n + 1)
| (n + 1) fi.zero := fi.zero
| (n + 1) (suc i) := suc (inject i)

def deg : Π {n} (i : fi (n + 1)), fi n → fi (n + 1)
| (n + 1) fi.zero fi.zero := suc (fi.zero)
| (n + 1) (suc i) fi.zero := fi.zero
| (n + 1) (suc i) (suc j) := suc (deg i j)
| (n + 1) fi.zero (suc j) := inject (inject j)

end fi



