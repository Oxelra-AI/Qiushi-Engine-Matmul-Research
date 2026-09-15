import QiushiGlobalOrbitData3

namespace QiushiMatmul.GlobalOrbit.Cases3
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem normalized48 : NormalizationCheck (frozenWangBasis 48) free48 := by
  decide +kernel +revert

theorem checked48 : ∀ k : Fin (2 ^ free48.length), TransitionCheck 48 (unpackCode free48 k.val) (rows48 k) := by
  decide +kernel +revert

theorem normalized49 : NormalizationCheck (frozenWangBasis 49) free49 := by
  decide +kernel +revert

theorem checked49 : ∀ k : Fin (2 ^ free49.length), TransitionCheck 49 (unpackCode free49 k.val) (rows49 k) := by
  decide +kernel +revert

theorem normalized50 : NormalizationCheck (frozenWangBasis 50) free50 := by
  decide +kernel +revert

theorem checked50 : ∀ k : Fin (2 ^ free50.length), TransitionCheck 50 (unpackCode free50 k.val) (rows50 k) := by
  decide +kernel +revert

theorem normalized51 : NormalizationCheck (frozenWangBasis 51) free51 := by
  decide +kernel +revert

theorem checked51 : ∀ k : Fin (2 ^ free51.length), TransitionCheck 51 (unpackCode free51 k.val) (rows51 k) := by
  decide +kernel +revert

theorem normalized52 : NormalizationCheck (frozenWangBasis 52) free52 := by
  decide +kernel +revert

theorem checked52 : ∀ k : Fin (2 ^ free52.length), TransitionCheck 52 (unpackCode free52 k.val) (rows52 k) := by
  decide +kernel +revert

theorem normalized53 : NormalizationCheck (frozenWangBasis 53) free53 := by
  decide +kernel +revert

theorem checked53 : ∀ k : Fin (2 ^ free53.length), TransitionCheck 53 (unpackCode free53 k.val) (rows53 k) := by
  decide +kernel +revert

theorem normalized54 : NormalizationCheck (frozenWangBasis 54) free54 := by
  decide +kernel +revert

theorem checked54 : ∀ k : Fin (2 ^ free54.length), TransitionCheck 54 (unpackCode free54 k.val) (rows54 k) := by
  decide +kernel +revert

theorem normalized55 : NormalizationCheck (frozenWangBasis 55) free55 := by
  decide +kernel +revert

theorem checked55 : ∀ k : Fin (2 ^ free55.length), TransitionCheck 55 (unpackCode free55 k.val) (rows55 k) := by
  decide +kernel +revert

theorem normalized56 : NormalizationCheck (frozenWangBasis 56) free56 := by
  decide +kernel +revert

theorem checked56 : ∀ k : Fin (2 ^ free56.length), TransitionCheck 56 (unpackCode free56 k.val) (rows56 k) := by
  decide +kernel +revert

theorem normalized57 : NormalizationCheck (frozenWangBasis 57) free57 := by
  decide +kernel +revert

theorem checked57 : ∀ k : Fin (2 ^ free57.length), TransitionCheck 57 (unpackCode free57 k.val) (rows57 k) := by
  decide +kernel +revert

theorem normalized58 : NormalizationCheck (frozenWangBasis 58) free58 := by
  decide +kernel +revert

theorem checked58 : ∀ k : Fin (2 ^ free58.length), TransitionCheck 58 (unpackCode free58 k.val) (rows58 k) := by
  decide +kernel +revert

theorem normalized59 : NormalizationCheck (frozenWangBasis 59) free59 := by
  decide +kernel +revert

theorem checked59 : ∀ k : Fin (2 ^ free59.length), TransitionCheck 59 (unpackCode free59 k.val) (rows59 k) := by
  decide +kernel +revert

theorem normalized60 : NormalizationCheck (frozenWangBasis 60) free60 := by
  decide +kernel +revert

theorem checked60 : ∀ k : Fin (2 ^ free60.length), TransitionCheck 60 (unpackCode free60 k.val) (rows60 k) := by
  decide +kernel +revert

theorem normalized61 : NormalizationCheck (frozenWangBasis 61) free61 := by
  decide +kernel +revert

theorem checked61 : ∀ k : Fin (2 ^ free61.length), TransitionCheck 61 (unpackCode free61 k.val) (rows61 k) := by
  decide +kernel +revert

theorem normalized62 : NormalizationCheck (frozenWangBasis 62) free62 := by
  decide +kernel +revert

theorem checked62 : ∀ k : Fin (2 ^ free62.length), TransitionCheck 62 (unpackCode free62 k.val) (rows62 k) := by
  decide +kernel +revert

theorem normalized63 : NormalizationCheck (frozenWangBasis 63) free63 := by
  decide +kernel +revert

theorem checked63 : ∀ k : Fin (2 ^ free63.length), TransitionCheck 63 (unpackCode free63 k.val) (rows63 k) := by
  decide +kernel +revert

theorem covered (j : Fin 16) : ∀ c : Fin 512,
    Covered (spanCodes (c.val :: frozenWangBasis ⟨48 + j.val, by omega⟩)) := by
  fin_cases j
  · exact extensions_of_normalized 48 free48 normalized48 rows48 checked48
  · exact extensions_of_normalized 49 free49 normalized49 rows49 checked49
  · exact extensions_of_normalized 50 free50 normalized50 rows50 checked50
  · exact extensions_of_normalized 51 free51 normalized51 rows51 checked51
  · exact extensions_of_normalized 52 free52 normalized52 rows52 checked52
  · exact extensions_of_normalized 53 free53 normalized53 rows53 checked53
  · exact extensions_of_normalized 54 free54 normalized54 rows54 checked54
  · exact extensions_of_normalized 55 free55 normalized55 rows55 checked55
  · exact extensions_of_normalized 56 free56 normalized56 rows56 checked56
  · exact extensions_of_normalized 57 free57 normalized57 rows57 checked57
  · exact extensions_of_normalized 58 free58 normalized58 rows58 checked58
  · exact extensions_of_normalized 59 free59 normalized59 rows59 checked59
  · exact extensions_of_normalized 60 free60 normalized60 rows60 checked60
  · exact extensions_of_normalized 61 free61 normalized61 rows61 checked61
  · exact extensions_of_normalized 62 free62 normalized62 rows62 checked62
  · exact extensions_of_normalized 63 free63 normalized63 rows63 checked63

end QiushiMatmul.GlobalOrbit.Cases3
