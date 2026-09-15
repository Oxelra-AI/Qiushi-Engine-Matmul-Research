import QiushiGlobalOrbitData8

namespace QiushiMatmul.GlobalOrbit.Cases8
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem normalized128 : NormalizationCheck (frozenWangBasis 128) free128 := by
  decide +kernel +revert

theorem checked128 : ∀ k : Fin (2 ^ free128.length), TransitionCheck 128 (unpackCode free128 k.val) (rows128 k) := by
  decide +kernel +revert

theorem normalized129 : NormalizationCheck (frozenWangBasis 129) free129 := by
  decide +kernel +revert

theorem checked129 : ∀ k : Fin (2 ^ free129.length), TransitionCheck 129 (unpackCode free129 k.val) (rows129 k) := by
  decide +kernel +revert

theorem normalized130 : NormalizationCheck (frozenWangBasis 130) free130 := by
  decide +kernel +revert

theorem checked130 : ∀ k : Fin (2 ^ free130.length), TransitionCheck 130 (unpackCode free130 k.val) (rows130 k) := by
  decide +kernel +revert

theorem normalized131 : NormalizationCheck (frozenWangBasis 131) free131 := by
  decide +kernel +revert

theorem checked131 : ∀ k : Fin (2 ^ free131.length), TransitionCheck 131 (unpackCode free131 k.val) (rows131 k) := by
  decide +kernel +revert

theorem normalized132 : NormalizationCheck (frozenWangBasis 132) free132 := by
  decide +kernel +revert

theorem checked132 : ∀ k : Fin (2 ^ free132.length), TransitionCheck 132 (unpackCode free132 k.val) (rows132 k) := by
  decide +kernel +revert

theorem normalized133 : NormalizationCheck (frozenWangBasis 133) free133 := by
  decide +kernel +revert

theorem checked133 : ∀ k : Fin (2 ^ free133.length), TransitionCheck 133 (unpackCode free133 k.val) (rows133 k) := by
  decide +kernel +revert

theorem normalized134 : NormalizationCheck (frozenWangBasis 134) free134 := by
  decide +kernel +revert

theorem checked134 : ∀ k : Fin (2 ^ free134.length), TransitionCheck 134 (unpackCode free134 k.val) (rows134 k) := by
  decide +kernel +revert

theorem normalized135 : NormalizationCheck (frozenWangBasis 135) free135 := by
  decide +kernel +revert

theorem checked135 : ∀ k : Fin (2 ^ free135.length), TransitionCheck 135 (unpackCode free135 k.val) (rows135 k) := by
  decide +kernel +revert

theorem normalized136 : NormalizationCheck (frozenWangBasis 136) free136 := by
  decide +kernel +revert

theorem checked136 : ∀ k : Fin (2 ^ free136.length), TransitionCheck 136 (unpackCode free136 k.val) (rows136 k) := by
  decide +kernel +revert

theorem normalized137 : NormalizationCheck (frozenWangBasis 137) free137 := by
  decide +kernel +revert

theorem checked137 : ∀ k : Fin (2 ^ free137.length), TransitionCheck 137 (unpackCode free137 k.val) (rows137 k) := by
  decide +kernel +revert

theorem normalized138 : NormalizationCheck (frozenWangBasis 138) free138 := by
  decide +kernel +revert

theorem checked138 : ∀ k : Fin (2 ^ free138.length), TransitionCheck 138 (unpackCode free138 k.val) (rows138 k) := by
  decide +kernel +revert

theorem normalized139 : NormalizationCheck (frozenWangBasis 139) free139 := by
  decide +kernel +revert

theorem checked139 : ∀ k : Fin (2 ^ free139.length), TransitionCheck 139 (unpackCode free139 k.val) (rows139 k) := by
  decide +kernel +revert

theorem normalized140 : NormalizationCheck (frozenWangBasis 140) free140 := by
  decide +kernel +revert

theorem checked140 : ∀ k : Fin (2 ^ free140.length), TransitionCheck 140 (unpackCode free140 k.val) (rows140 k) := by
  decide +kernel +revert

theorem normalized141 : NormalizationCheck (frozenWangBasis 141) free141 := by
  decide +kernel +revert

theorem checked141 : ∀ k : Fin (2 ^ free141.length), TransitionCheck 141 (unpackCode free141 k.val) (rows141 k) := by
  decide +kernel +revert

theorem normalized142 : NormalizationCheck (frozenWangBasis 142) free142 := by
  decide +kernel +revert

theorem checked142 : ∀ k : Fin (2 ^ free142.length), TransitionCheck 142 (unpackCode free142 k.val) (rows142 k) := by
  decide +kernel +revert

theorem normalized143 : NormalizationCheck (frozenWangBasis 143) free143 := by
  decide +kernel +revert

theorem checked143 : ∀ k : Fin (2 ^ free143.length), TransitionCheck 143 (unpackCode free143 k.val) (rows143 k) := by
  decide +kernel +revert

theorem covered (j : Fin 16) : ∀ c : Fin 512,
    Covered (spanCodes (c.val :: frozenWangBasis ⟨128 + j.val, by omega⟩)) := by
  fin_cases j
  · exact extensions_of_normalized 128 free128 normalized128 rows128 checked128
  · exact extensions_of_normalized 129 free129 normalized129 rows129 checked129
  · exact extensions_of_normalized 130 free130 normalized130 rows130 checked130
  · exact extensions_of_normalized 131 free131 normalized131 rows131 checked131
  · exact extensions_of_normalized 132 free132 normalized132 rows132 checked132
  · exact extensions_of_normalized 133 free133 normalized133 rows133 checked133
  · exact extensions_of_normalized 134 free134 normalized134 rows134 checked134
  · exact extensions_of_normalized 135 free135 normalized135 rows135 checked135
  · exact extensions_of_normalized 136 free136 normalized136 rows136 checked136
  · exact extensions_of_normalized 137 free137 normalized137 rows137 checked137
  · exact extensions_of_normalized 138 free138 normalized138 rows138 checked138
  · exact extensions_of_normalized 139 free139 normalized139 rows139 checked139
  · exact extensions_of_normalized 140 free140 normalized140 rows140 checked140
  · exact extensions_of_normalized 141 free141 normalized141 rows141 checked141
  · exact extensions_of_normalized 142 free142 normalized142 rows142 checked142
  · exact extensions_of_normalized 143 free143 normalized143 rows143 checked143

end QiushiMatmul.GlobalOrbit.Cases8
