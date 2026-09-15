import QiushiReport

set_option autoImplicit false

noncomputable section

open QiushiMatmul

example : RankAtLeast 21 := rank_ge_21

example (i : Fin 496) :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis i))
      (frozenWangTable.lower i) := FrozenRegistry.all_representatives i

example (W : Submodule F2 Mat3) :
    QuotientRankAtLeast W (frozenWangTable.L0 W) := FrozenRegistry.L0_rank_sound W

/-- info: 'QiushiMatmul.FrozenRegistry.L0_rank_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FrozenRegistry.L0_rank_sound

example : (∀ W : Submodule F2 Mat3, GlobalOrbit.Covered W) ↔
    GlobalOrbit.ExtensionChecks := GlobalOrbit.global_coverage_iff_extensions

example (W : Submodule F2 Mat3) :
    ∃ i : Fin 496, frozenWangTable.OrbitImage i W := GlobalOrbit.frozen_coverage W

/-- info: 'QiushiMatmul.GlobalOrbit.frozen_coverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GlobalOrbit.frozen_coverage

example (r : Nat) : Nonempty (QuotientTensorDecomp (spanCodes [4,2,1]) r) ↔
    Nonempty (RectTensorDecomp r) := firstRow_quotient_decomp_iff r
