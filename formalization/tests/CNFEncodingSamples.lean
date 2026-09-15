import QiushiCardinalityCNF
import QiushiExactPrefixCNF
import Lean.Data.Json

/-! Executable cross-check samples only; theorem proofs do not depend on this output. -/
namespace Qiushi.CNF.Samples
open Std.Sat Lean

def dimacsLiteral (n K : Nat) (l : Literal CounterVar) : Int :=
  let id := match l.1 with
    | .inl i => i+1
    | .inr (i,j) => n+1+i*(K+1)+j
  if l.2 then (id : Int) else -(id : Int)

def record (kind : String) (n k : Nat) (f : CNF CounterVar) (K : Nat) : Json :=
  Json.mkObj [("kind", toJson kind), ("n", toJson n), ("k", toJson k),
    ("clauses", toJson (f.clauses.map (fun c => c.map (dimacsLiteral n K))))]

#eval do
  for n in List.range 5 do
    for k in List.range (n+3) do
      let cap : Int := Int.ofNat k - 1
      let sample := record "row" n k (rowCNF n cap) (cap.toNat+1)
      IO.println sample.compress
  for n in List.range 5 do
    for k in List.range (n+2) do
      IO.println (record "exact" n k (exactPrefixCNF n k) (k+1)).compress

end Qiushi.CNF.Samples
