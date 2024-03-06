inductive MyUnderyNat : Type
| O : MyUnderyNat
| Succ : MyUnderyNat -> MyUnderyNat

def add : MyUnderyNat -> MyUnderyNat -> MyUnderyNat
| MyUnderyNat.O, n => n
| MyUnderyNat.Succ m, n => MyUnderyNat.Succ (add m n)

def add' (m n : MyUnderyNat) : MyUnderyNat :=
  match m with
  | O => n
  | Succ m' => Succ (add' m' n)
