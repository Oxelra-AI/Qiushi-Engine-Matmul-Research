import QiushiFrozenRank357

open QiushiMatmul QiushiMatmul.FrozenRank BigOperators

example : QuotientRankAtLeast (spanCodes [298,96,20,1]) 17 := span357_lb17

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 357))
    (frozenWangTable.lower 357) := rep357

example (i : Fin 13) : QuotientRankAtLeast (spanCodes (sources357 i)) (lower357 i) :=
  sources357_rank i

example (r : Nat) (hr : r < 17) (hlower : ∀ i, lower357 i ≤ r) :
    (∑ i : Fin 13, (r - lower357 i)) < r := capacity357 r hr hlower

example : ∀ c : Fin 512, ∃ i : Fin 13,
    spanContainsCode (sources357 i) c.val = true := sources357_cover

/-- info: 'QiushiMatmul.FrozenRank.sources357_rank' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sources357_rank

/-- info: 'QiushiMatmul.FrozenRank.span357_lb17' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms span357_lb17

/-- info: 'QiushiMatmul.FrozenRank.rep357' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rep357
