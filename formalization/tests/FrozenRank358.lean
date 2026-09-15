import QiushiFrozenRank358

open QiushiMatmul QiushiMatmul.FrozenRank BigOperators

example : QuotientRankAtLeast (spanCodes [386,96,20,1]) 17 := span358_lb17

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 358))
    (frozenWangTable.lower 358) := rep358

example (i : Fin 10) : QuotientRankAtLeast (spanCodes (sources358 i)) (lower358 i) :=
  sources358_rank i

example (r : Nat) (hr : r < 17) (hlower : ∀ i, lower358 i ≤ r) :
    (∑ i : Fin 10, (r - lower358 i)) < r := capacity358 r hr hlower

example : ∀ c : Fin 512, ∃ i : Fin 10,
    spanContainsCode (sources358 i) c.val = true := sources358_cover

/-- info: 'QiushiMatmul.FrozenRank.sources358_rank' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sources358_rank

/-- info: 'QiushiMatmul.FrozenRank.span358_lb17' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms span358_lb17

/-- info: 'QiushiMatmul.FrozenRank.rep358' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rep358
