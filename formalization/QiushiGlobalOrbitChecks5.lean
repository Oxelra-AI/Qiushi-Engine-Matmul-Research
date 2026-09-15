import QiushiGlobalOrbitData5

namespace QiushiMatmul.GlobalOrbit.Cases5
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem normalized80 : NormalizationCheck (frozenWangBasis 80) free80 := by
  decide +kernel +revert

theorem checked80 : ∀ k : Fin (2 ^ free80.length), TransitionCheck 80 (unpackCode free80 k.val) (rows80 k) := by
  decide +kernel +revert

theorem normalized81 : NormalizationCheck (frozenWangBasis 81) free81 := by
  decide +kernel +revert

theorem checked81 : ∀ k : Fin (2 ^ free81.length), TransitionCheck 81 (unpackCode free81 k.val) (rows81 k) := by
  decide +kernel +revert

theorem normalized82 : NormalizationCheck (frozenWangBasis 82) free82 := by
  decide +kernel +revert

theorem checked82 : ∀ k : Fin (2 ^ free82.length), TransitionCheck 82 (unpackCode free82 k.val) (rows82 k) := by
  decide +kernel +revert

theorem normalized83 : NormalizationCheck (frozenWangBasis 83) free83 := by
  decide +kernel +revert

theorem checked83 : ∀ k : Fin (2 ^ free83.length), TransitionCheck 83 (unpackCode free83 k.val) (rows83 k) := by
  decide +kernel +revert

theorem normalized84 : NormalizationCheck (frozenWangBasis 84) free84 := by
  decide +kernel +revert

theorem checked84 : ∀ k : Fin (2 ^ free84.length), TransitionCheck 84 (unpackCode free84 k.val) (rows84 k) := by
  decide +kernel +revert

theorem normalized85 : NormalizationCheck (frozenWangBasis 85) free85 := by
  decide +kernel +revert

theorem checked85 : ∀ k : Fin (2 ^ free85.length), TransitionCheck 85 (unpackCode free85 k.val) (rows85 k) := by
  decide +kernel +revert

theorem normalized86 : NormalizationCheck (frozenWangBasis 86) free86 := by
  decide +kernel +revert

theorem checked86 : ∀ k : Fin (2 ^ free86.length), TransitionCheck 86 (unpackCode free86 k.val) (rows86 k) := by
  decide +kernel +revert

theorem normalized87 : NormalizationCheck (frozenWangBasis 87) free87 := by
  decide +kernel +revert

theorem checked87 : ∀ k : Fin (2 ^ free87.length), TransitionCheck 87 (unpackCode free87 k.val) (rows87 k) := by
  decide +kernel +revert

theorem normalized88 : NormalizationCheck (frozenWangBasis 88) free88 := by
  decide +kernel +revert

theorem checked88 : ∀ k : Fin (2 ^ free88.length), TransitionCheck 88 (unpackCode free88 k.val) (rows88 k) := by
  decide +kernel +revert

theorem normalized89 : NormalizationCheck (frozenWangBasis 89) free89 := by
  decide +kernel +revert

theorem checked89 : ∀ k : Fin (2 ^ free89.length), TransitionCheck 89 (unpackCode free89 k.val) (rows89 k) := by
  decide +kernel +revert

theorem normalized90 : NormalizationCheck (frozenWangBasis 90) free90 := by
  decide +kernel +revert

theorem checked90 : ∀ k : Fin (2 ^ free90.length), TransitionCheck 90 (unpackCode free90 k.val) (rows90 k) := by
  decide +kernel +revert

theorem normalized91 : NormalizationCheck (frozenWangBasis 91) free91 := by
  decide +kernel +revert

theorem checked91 : ∀ k : Fin (2 ^ free91.length), TransitionCheck 91 (unpackCode free91 k.val) (rows91 k) := by
  decide +kernel +revert

theorem normalized92 : NormalizationCheck (frozenWangBasis 92) free92 := by
  decide +kernel +revert

theorem checked92 : ∀ k : Fin (2 ^ free92.length), TransitionCheck 92 (unpackCode free92 k.val) (rows92 k) := by
  decide +kernel +revert

theorem normalized93 : NormalizationCheck (frozenWangBasis 93) free93 := by
  decide +kernel +revert

theorem checked93 : ∀ k : Fin (2 ^ free93.length), TransitionCheck 93 (unpackCode free93 k.val) (rows93 k) := by
  decide +kernel +revert

theorem normalized94 : NormalizationCheck (frozenWangBasis 94) free94 := by
  decide +kernel +revert

theorem checked94 : ∀ k : Fin (2 ^ free94.length), TransitionCheck 94 (unpackCode free94 k.val) (rows94 k) := by
  decide +kernel +revert

theorem normalized95 : NormalizationCheck (frozenWangBasis 95) free95 := by
  decide +kernel +revert

theorem checked95 : ∀ k : Fin (2 ^ free95.length), TransitionCheck 95 (unpackCode free95 k.val) (rows95 k) := by
  decide +kernel +revert

theorem covered (j : Fin 16) : ∀ c : Fin 512,
    Covered (spanCodes (c.val :: frozenWangBasis ⟨80 + j.val, by omega⟩)) := by
  fin_cases j
  · exact extensions_of_normalized 80 free80 normalized80 rows80 checked80
  · exact extensions_of_normalized 81 free81 normalized81 rows81 checked81
  · exact extensions_of_normalized 82 free82 normalized82 rows82 checked82
  · exact extensions_of_normalized 83 free83 normalized83 rows83 checked83
  · exact extensions_of_normalized 84 free84 normalized84 rows84 checked84
  · exact extensions_of_normalized 85 free85 normalized85 rows85 checked85
  · exact extensions_of_normalized 86 free86 normalized86 rows86 checked86
  · exact extensions_of_normalized 87 free87 normalized87 rows87 checked87
  · exact extensions_of_normalized 88 free88 normalized88 rows88 checked88
  · exact extensions_of_normalized 89 free89 normalized89 rows89 checked89
  · exact extensions_of_normalized 90 free90 normalized90 rows90 checked90
  · exact extensions_of_normalized 91 free91 normalized91 rows91 checked91
  · exact extensions_of_normalized 92 free92 normalized92 rows92 checked92
  · exact extensions_of_normalized 93 free93 normalized93 rows93 checked93
  · exact extensions_of_normalized 94 free94 normalized94 rows94 checked94
  · exact extensions_of_normalized 95 free95 normalized95 rows95 checked95

end QiushiMatmul.GlobalOrbit.Cases5
