import QiushiGlobalOrbitData7

namespace QiushiMatmul.GlobalOrbit.Cases7
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem normalized112 : NormalizationCheck (frozenWangBasis 112) free112 := by
  decide +kernel +revert

theorem checked112 : ∀ k : Fin (2 ^ free112.length), TransitionCheck 112 (unpackCode free112 k.val) (rows112 k) := by
  decide +kernel +revert

theorem normalized113 : NormalizationCheck (frozenWangBasis 113) free113 := by
  decide +kernel +revert

theorem checked113 : ∀ k : Fin (2 ^ free113.length), TransitionCheck 113 (unpackCode free113 k.val) (rows113 k) := by
  decide +kernel +revert

theorem normalized114 : NormalizationCheck (frozenWangBasis 114) free114 := by
  decide +kernel +revert

theorem checked114 : ∀ k : Fin (2 ^ free114.length), TransitionCheck 114 (unpackCode free114 k.val) (rows114 k) := by
  decide +kernel +revert

theorem normalized115 : NormalizationCheck (frozenWangBasis 115) free115 := by
  decide +kernel +revert

theorem checked115 : ∀ k : Fin (2 ^ free115.length), TransitionCheck 115 (unpackCode free115 k.val) (rows115 k) := by
  decide +kernel +revert

theorem normalized116 : NormalizationCheck (frozenWangBasis 116) free116 := by
  decide +kernel +revert

theorem checked116 : ∀ k : Fin (2 ^ free116.length), TransitionCheck 116 (unpackCode free116 k.val) (rows116 k) := by
  decide +kernel +revert

theorem normalized117 : NormalizationCheck (frozenWangBasis 117) free117 := by
  decide +kernel +revert

theorem checked117 : ∀ k : Fin (2 ^ free117.length), TransitionCheck 117 (unpackCode free117 k.val) (rows117 k) := by
  decide +kernel +revert

theorem normalized118 : NormalizationCheck (frozenWangBasis 118) free118 := by
  decide +kernel +revert

theorem checked118 : ∀ k : Fin (2 ^ free118.length), TransitionCheck 118 (unpackCode free118 k.val) (rows118 k) := by
  decide +kernel +revert

theorem normalized119 : NormalizationCheck (frozenWangBasis 119) free119 := by
  decide +kernel +revert

theorem checked119 : ∀ k : Fin (2 ^ free119.length), TransitionCheck 119 (unpackCode free119 k.val) (rows119 k) := by
  decide +kernel +revert

theorem normalized120 : NormalizationCheck (frozenWangBasis 120) free120 := by
  decide +kernel +revert

theorem checked120 : ∀ k : Fin (2 ^ free120.length), TransitionCheck 120 (unpackCode free120 k.val) (rows120 k) := by
  decide +kernel +revert

theorem normalized121 : NormalizationCheck (frozenWangBasis 121) free121 := by
  decide +kernel +revert

theorem checked121 : ∀ k : Fin (2 ^ free121.length), TransitionCheck 121 (unpackCode free121 k.val) (rows121 k) := by
  decide +kernel +revert

theorem normalized122 : NormalizationCheck (frozenWangBasis 122) free122 := by
  decide +kernel +revert

theorem checked122 : ∀ k : Fin (2 ^ free122.length), TransitionCheck 122 (unpackCode free122 k.val) (rows122 k) := by
  decide +kernel +revert

theorem normalized123 : NormalizationCheck (frozenWangBasis 123) free123 := by
  decide +kernel +revert

theorem checked123 : ∀ k : Fin (2 ^ free123.length), TransitionCheck 123 (unpackCode free123 k.val) (rows123 k) := by
  decide +kernel +revert

theorem normalized124 : NormalizationCheck (frozenWangBasis 124) free124 := by
  decide +kernel +revert

theorem checked124 : ∀ k : Fin (2 ^ free124.length), TransitionCheck 124 (unpackCode free124 k.val) (rows124 k) := by
  decide +kernel +revert

theorem normalized125 : NormalizationCheck (frozenWangBasis 125) free125 := by
  decide +kernel +revert

theorem checked125 : ∀ k : Fin (2 ^ free125.length), TransitionCheck 125 (unpackCode free125 k.val) (rows125 k) := by
  decide +kernel +revert

theorem normalized126 : NormalizationCheck (frozenWangBasis 126) free126 := by
  decide +kernel +revert

theorem checked126 : ∀ k : Fin (2 ^ free126.length), TransitionCheck 126 (unpackCode free126 k.val) (rows126 k) := by
  decide +kernel +revert

theorem normalized127 : NormalizationCheck (frozenWangBasis 127) free127 := by
  decide +kernel +revert

theorem checked127 : ∀ k : Fin (2 ^ free127.length), TransitionCheck 127 (unpackCode free127 k.val) (rows127 k) := by
  decide +kernel +revert

theorem covered (j : Fin 16) : ∀ c : Fin 512,
    Covered (spanCodes (c.val :: frozenWangBasis ⟨112 + j.val, by omega⟩)) := by
  fin_cases j
  · exact extensions_of_normalized 112 free112 normalized112 rows112 checked112
  · exact extensions_of_normalized 113 free113 normalized113 rows113 checked113
  · exact extensions_of_normalized 114 free114 normalized114 rows114 checked114
  · exact extensions_of_normalized 115 free115 normalized115 rows115 checked115
  · exact extensions_of_normalized 116 free116 normalized116 rows116 checked116
  · exact extensions_of_normalized 117 free117 normalized117 rows117 checked117
  · exact extensions_of_normalized 118 free118 normalized118 rows118 checked118
  · exact extensions_of_normalized 119 free119 normalized119 rows119 checked119
  · exact extensions_of_normalized 120 free120 normalized120 rows120 checked120
  · exact extensions_of_normalized 121 free121 normalized121 rows121 checked121
  · exact extensions_of_normalized 122 free122 normalized122 rows122 checked122
  · exact extensions_of_normalized 123 free123 normalized123 rows123 checked123
  · exact extensions_of_normalized 124 free124 normalized124 rows124 checked124
  · exact extensions_of_normalized 125 free125 normalized125 rows125 checked125
  · exact extensions_of_normalized 126 free126 normalized126 rows126 checked126
  · exact extensions_of_normalized 127 free127 normalized127 rows127 checked127

end QiushiMatmul.GlobalOrbit.Cases7
