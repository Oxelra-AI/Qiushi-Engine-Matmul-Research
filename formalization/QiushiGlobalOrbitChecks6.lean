import QiushiGlobalOrbitData6

namespace QiushiMatmul.GlobalOrbit.Cases6
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem normalized96 : NormalizationCheck (frozenWangBasis 96) free96 := by
  decide +kernel +revert

theorem checked96 : ∀ k : Fin (2 ^ free96.length), TransitionCheck 96 (unpackCode free96 k.val) (rows96 k) := by
  decide +kernel +revert

theorem normalized97 : NormalizationCheck (frozenWangBasis 97) free97 := by
  decide +kernel +revert

theorem checked97 : ∀ k : Fin (2 ^ free97.length), TransitionCheck 97 (unpackCode free97 k.val) (rows97 k) := by
  decide +kernel +revert

theorem normalized98 : NormalizationCheck (frozenWangBasis 98) free98 := by
  decide +kernel +revert

theorem checked98 : ∀ k : Fin (2 ^ free98.length), TransitionCheck 98 (unpackCode free98 k.val) (rows98 k) := by
  decide +kernel +revert

theorem normalized99 : NormalizationCheck (frozenWangBasis 99) free99 := by
  decide +kernel +revert

theorem checked99 : ∀ k : Fin (2 ^ free99.length), TransitionCheck 99 (unpackCode free99 k.val) (rows99 k) := by
  decide +kernel +revert

theorem normalized100 : NormalizationCheck (frozenWangBasis 100) free100 := by
  decide +kernel +revert

theorem checked100 : ∀ k : Fin (2 ^ free100.length), TransitionCheck 100 (unpackCode free100 k.val) (rows100 k) := by
  decide +kernel +revert

theorem normalized101 : NormalizationCheck (frozenWangBasis 101) free101 := by
  decide +kernel +revert

theorem checked101 : ∀ k : Fin (2 ^ free101.length), TransitionCheck 101 (unpackCode free101 k.val) (rows101 k) := by
  decide +kernel +revert

theorem normalized102 : NormalizationCheck (frozenWangBasis 102) free102 := by
  decide +kernel +revert

theorem checked102 : ∀ k : Fin (2 ^ free102.length), TransitionCheck 102 (unpackCode free102 k.val) (rows102 k) := by
  decide +kernel +revert

theorem normalized103 : NormalizationCheck (frozenWangBasis 103) free103 := by
  decide +kernel +revert

theorem checked103 : ∀ k : Fin (2 ^ free103.length), TransitionCheck 103 (unpackCode free103 k.val) (rows103 k) := by
  decide +kernel +revert

theorem normalized104 : NormalizationCheck (frozenWangBasis 104) free104 := by
  decide +kernel +revert

theorem checked104 : ∀ k : Fin (2 ^ free104.length), TransitionCheck 104 (unpackCode free104 k.val) (rows104 k) := by
  decide +kernel +revert

theorem normalized105 : NormalizationCheck (frozenWangBasis 105) free105 := by
  decide +kernel +revert

theorem checked105 : ∀ k : Fin (2 ^ free105.length), TransitionCheck 105 (unpackCode free105 k.val) (rows105 k) := by
  decide +kernel +revert

theorem normalized106 : NormalizationCheck (frozenWangBasis 106) free106 := by
  decide +kernel +revert

theorem checked106 : ∀ k : Fin (2 ^ free106.length), TransitionCheck 106 (unpackCode free106 k.val) (rows106 k) := by
  decide +kernel +revert

theorem normalized107 : NormalizationCheck (frozenWangBasis 107) free107 := by
  decide +kernel +revert

theorem checked107 : ∀ k : Fin (2 ^ free107.length), TransitionCheck 107 (unpackCode free107 k.val) (rows107 k) := by
  decide +kernel +revert

theorem normalized108 : NormalizationCheck (frozenWangBasis 108) free108 := by
  decide +kernel +revert

theorem checked108 : ∀ k : Fin (2 ^ free108.length), TransitionCheck 108 (unpackCode free108 k.val) (rows108 k) := by
  decide +kernel +revert

theorem normalized109 : NormalizationCheck (frozenWangBasis 109) free109 := by
  decide +kernel +revert

theorem checked109 : ∀ k : Fin (2 ^ free109.length), TransitionCheck 109 (unpackCode free109 k.val) (rows109 k) := by
  decide +kernel +revert

theorem normalized110 : NormalizationCheck (frozenWangBasis 110) free110 := by
  decide +kernel +revert

theorem checked110 : ∀ k : Fin (2 ^ free110.length), TransitionCheck 110 (unpackCode free110 k.val) (rows110 k) := by
  decide +kernel +revert

theorem normalized111 : NormalizationCheck (frozenWangBasis 111) free111 := by
  decide +kernel +revert

theorem checked111 : ∀ k : Fin (2 ^ free111.length), TransitionCheck 111 (unpackCode free111 k.val) (rows111 k) := by
  decide +kernel +revert

theorem covered (j : Fin 16) : ∀ c : Fin 512,
    Covered (spanCodes (c.val :: frozenWangBasis ⟨96 + j.val, by omega⟩)) := by
  fin_cases j
  · exact extensions_of_normalized 96 free96 normalized96 rows96 checked96
  · exact extensions_of_normalized 97 free97 normalized97 rows97 checked97
  · exact extensions_of_normalized 98 free98 normalized98 rows98 checked98
  · exact extensions_of_normalized 99 free99 normalized99 rows99 checked99
  · exact extensions_of_normalized 100 free100 normalized100 rows100 checked100
  · exact extensions_of_normalized 101 free101 normalized101 rows101 checked101
  · exact extensions_of_normalized 102 free102 normalized102 rows102 checked102
  · exact extensions_of_normalized 103 free103 normalized103 rows103 checked103
  · exact extensions_of_normalized 104 free104 normalized104 rows104 checked104
  · exact extensions_of_normalized 105 free105 normalized105 rows105 checked105
  · exact extensions_of_normalized 106 free106 normalized106 rows106 checked106
  · exact extensions_of_normalized 107 free107 normalized107 rows107 checked107
  · exact extensions_of_normalized 108 free108 normalized108 rows108 checked108
  · exact extensions_of_normalized 109 free109 normalized109 rows109 checked109
  · exact extensions_of_normalized 110 free110 normalized110 rows110 checked110
  · exact extensions_of_normalized 111 free111 normalized111 rows111 checked111

end QiushiMatmul.GlobalOrbit.Cases6
