import QiushiGlobalOrbitData4

namespace QiushiMatmul.GlobalOrbit.Cases4
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem normalized64 : NormalizationCheck (frozenWangBasis 64) free64 := by
  decide +kernel +revert

theorem checked64 : ∀ k : Fin (2 ^ free64.length), TransitionCheck 64 (unpackCode free64 k.val) (rows64 k) := by
  decide +kernel +revert

theorem normalized65 : NormalizationCheck (frozenWangBasis 65) free65 := by
  decide +kernel +revert

theorem checked65 : ∀ k : Fin (2 ^ free65.length), TransitionCheck 65 (unpackCode free65 k.val) (rows65 k) := by
  decide +kernel +revert

theorem normalized66 : NormalizationCheck (frozenWangBasis 66) free66 := by
  decide +kernel +revert

theorem checked66 : ∀ k : Fin (2 ^ free66.length), TransitionCheck 66 (unpackCode free66 k.val) (rows66 k) := by
  decide +kernel +revert

theorem normalized67 : NormalizationCheck (frozenWangBasis 67) free67 := by
  decide +kernel +revert

theorem checked67 : ∀ k : Fin (2 ^ free67.length), TransitionCheck 67 (unpackCode free67 k.val) (rows67 k) := by
  decide +kernel +revert

theorem normalized68 : NormalizationCheck (frozenWangBasis 68) free68 := by
  decide +kernel +revert

theorem checked68 : ∀ k : Fin (2 ^ free68.length), TransitionCheck 68 (unpackCode free68 k.val) (rows68 k) := by
  decide +kernel +revert

theorem normalized69 : NormalizationCheck (frozenWangBasis 69) free69 := by
  decide +kernel +revert

theorem checked69 : ∀ k : Fin (2 ^ free69.length), TransitionCheck 69 (unpackCode free69 k.val) (rows69 k) := by
  decide +kernel +revert

theorem normalized70 : NormalizationCheck (frozenWangBasis 70) free70 := by
  decide +kernel +revert

theorem checked70 : ∀ k : Fin (2 ^ free70.length), TransitionCheck 70 (unpackCode free70 k.val) (rows70 k) := by
  decide +kernel +revert

theorem normalized71 : NormalizationCheck (frozenWangBasis 71) free71 := by
  decide +kernel +revert

theorem checked71 : ∀ k : Fin (2 ^ free71.length), TransitionCheck 71 (unpackCode free71 k.val) (rows71 k) := by
  decide +kernel +revert

theorem normalized72 : NormalizationCheck (frozenWangBasis 72) free72 := by
  decide +kernel +revert

theorem checked72 : ∀ k : Fin (2 ^ free72.length), TransitionCheck 72 (unpackCode free72 k.val) (rows72 k) := by
  decide +kernel +revert

theorem normalized73 : NormalizationCheck (frozenWangBasis 73) free73 := by
  decide +kernel +revert

theorem checked73 : ∀ k : Fin (2 ^ free73.length), TransitionCheck 73 (unpackCode free73 k.val) (rows73 k) := by
  decide +kernel +revert

theorem normalized74 : NormalizationCheck (frozenWangBasis 74) free74 := by
  decide +kernel +revert

theorem checked74 : ∀ k : Fin (2 ^ free74.length), TransitionCheck 74 (unpackCode free74 k.val) (rows74 k) := by
  decide +kernel +revert

theorem normalized75 : NormalizationCheck (frozenWangBasis 75) free75 := by
  decide +kernel +revert

theorem checked75 : ∀ k : Fin (2 ^ free75.length), TransitionCheck 75 (unpackCode free75 k.val) (rows75 k) := by
  decide +kernel +revert

theorem normalized76 : NormalizationCheck (frozenWangBasis 76) free76 := by
  decide +kernel +revert

theorem checked76 : ∀ k : Fin (2 ^ free76.length), TransitionCheck 76 (unpackCode free76 k.val) (rows76 k) := by
  decide +kernel +revert

theorem normalized77 : NormalizationCheck (frozenWangBasis 77) free77 := by
  decide +kernel +revert

theorem checked77 : ∀ k : Fin (2 ^ free77.length), TransitionCheck 77 (unpackCode free77 k.val) (rows77 k) := by
  decide +kernel +revert

theorem normalized78 : NormalizationCheck (frozenWangBasis 78) free78 := by
  decide +kernel +revert

theorem checked78 : ∀ k : Fin (2 ^ free78.length), TransitionCheck 78 (unpackCode free78 k.val) (rows78 k) := by
  decide +kernel +revert

theorem normalized79 : NormalizationCheck (frozenWangBasis 79) free79 := by
  decide +kernel +revert

theorem checked79 : ∀ k : Fin (2 ^ free79.length), TransitionCheck 79 (unpackCode free79 k.val) (rows79 k) := by
  decide +kernel +revert

theorem covered (j : Fin 16) : ∀ c : Fin 512,
    Covered (spanCodes (c.val :: frozenWangBasis ⟨64 + j.val, by omega⟩)) := by
  fin_cases j
  · exact extensions_of_normalized 64 free64 normalized64 rows64 checked64
  · exact extensions_of_normalized 65 free65 normalized65 rows65 checked65
  · exact extensions_of_normalized 66 free66 normalized66 rows66 checked66
  · exact extensions_of_normalized 67 free67 normalized67 rows67 checked67
  · exact extensions_of_normalized 68 free68 normalized68 rows68 checked68
  · exact extensions_of_normalized 69 free69 normalized69 rows69 checked69
  · exact extensions_of_normalized 70 free70 normalized70 rows70 checked70
  · exact extensions_of_normalized 71 free71 normalized71 rows71 checked71
  · exact extensions_of_normalized 72 free72 normalized72 rows72 checked72
  · exact extensions_of_normalized 73 free73 normalized73 rows73 checked73
  · exact extensions_of_normalized 74 free74 normalized74 rows74 checked74
  · exact extensions_of_normalized 75 free75 normalized75 rows75 checked75
  · exact extensions_of_normalized 76 free76 normalized76 rows76 checked76
  · exact extensions_of_normalized 77 free77 normalized77 rows77 checked77
  · exact extensions_of_normalized 78 free78 normalized78 rows78 checked78
  · exact extensions_of_normalized 79 free79 normalized79 rows79 checked79

end QiushiMatmul.GlobalOrbit.Cases4
