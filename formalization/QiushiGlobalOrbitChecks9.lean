import QiushiGlobalOrbitData9

namespace QiushiMatmul.GlobalOrbit.Cases9
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem normalized144 : NormalizationCheck (frozenWangBasis 144) free144 := by
  decide +kernel +revert

theorem checked144 : ∀ k : Fin (2 ^ free144.length), TransitionCheck 144 (unpackCode free144 k.val) (rows144 k) := by
  decide +kernel +revert

theorem normalized145 : NormalizationCheck (frozenWangBasis 145) free145 := by
  decide +kernel +revert

theorem checked145 : ∀ k : Fin (2 ^ free145.length), TransitionCheck 145 (unpackCode free145 k.val) (rows145 k) := by
  decide +kernel +revert

theorem normalized146 : NormalizationCheck (frozenWangBasis 146) free146 := by
  decide +kernel +revert

theorem checked146 : ∀ k : Fin (2 ^ free146.length), TransitionCheck 146 (unpackCode free146 k.val) (rows146 k) := by
  decide +kernel +revert

theorem normalized147 : NormalizationCheck (frozenWangBasis 147) free147 := by
  decide +kernel +revert

theorem checked147 : ∀ k : Fin (2 ^ free147.length), TransitionCheck 147 (unpackCode free147 k.val) (rows147 k) := by
  decide +kernel +revert

theorem normalized148 : NormalizationCheck (frozenWangBasis 148) free148 := by
  decide +kernel +revert

theorem checked148 : ∀ k : Fin (2 ^ free148.length), TransitionCheck 148 (unpackCode free148 k.val) (rows148 k) := by
  decide +kernel +revert

theorem normalized149 : NormalizationCheck (frozenWangBasis 149) free149 := by
  decide +kernel +revert

theorem checked149 : ∀ k : Fin (2 ^ free149.length), TransitionCheck 149 (unpackCode free149 k.val) (rows149 k) := by
  decide +kernel +revert

theorem normalized150 : NormalizationCheck (frozenWangBasis 150) free150 := by
  decide +kernel +revert

theorem checked150 : ∀ k : Fin (2 ^ free150.length), TransitionCheck 150 (unpackCode free150 k.val) (rows150 k) := by
  decide +kernel +revert

theorem normalized151 : NormalizationCheck (frozenWangBasis 151) free151 := by
  decide +kernel +revert

theorem checked151 : ∀ k : Fin (2 ^ free151.length), TransitionCheck 151 (unpackCode free151 k.val) (rows151 k) := by
  decide +kernel +revert

theorem normalized152 : NormalizationCheck (frozenWangBasis 152) free152 := by
  decide +kernel +revert

theorem checked152 : ∀ k : Fin (2 ^ free152.length), TransitionCheck 152 (unpackCode free152 k.val) (rows152 k) := by
  decide +kernel +revert

theorem normalized153 : NormalizationCheck (frozenWangBasis 153) free153 := by
  decide +kernel +revert

theorem checked153 : ∀ k : Fin (2 ^ free153.length), TransitionCheck 153 (unpackCode free153 k.val) (rows153 k) := by
  decide +kernel +revert

theorem normalized154 : NormalizationCheck (frozenWangBasis 154) free154 := by
  decide +kernel +revert

theorem checked154 : ∀ k : Fin (2 ^ free154.length), TransitionCheck 154 (unpackCode free154 k.val) (rows154 k) := by
  decide +kernel +revert

theorem normalized155 : NormalizationCheck (frozenWangBasis 155) free155 := by
  decide +kernel +revert

theorem checked155 : ∀ k : Fin (2 ^ free155.length), TransitionCheck 155 (unpackCode free155 k.val) (rows155 k) := by
  decide +kernel +revert

theorem normalized156 : NormalizationCheck (frozenWangBasis 156) free156 := by
  decide +kernel +revert

theorem checked156 : ∀ k : Fin (2 ^ free156.length), TransitionCheck 156 (unpackCode free156 k.val) (rows156 k) := by
  decide +kernel +revert

theorem normalized157 : NormalizationCheck (frozenWangBasis 157) free157 := by
  decide +kernel +revert

theorem checked157 : ∀ k : Fin (2 ^ free157.length), TransitionCheck 157 (unpackCode free157 k.val) (rows157 k) := by
  decide +kernel +revert

theorem normalized158 : NormalizationCheck (frozenWangBasis 158) free158 := by
  decide +kernel +revert

theorem checked158 : ∀ k : Fin (2 ^ free158.length), TransitionCheck 158 (unpackCode free158 k.val) (rows158 k) := by
  decide +kernel +revert

theorem normalized159 : NormalizationCheck (frozenWangBasis 159) free159 := by
  decide +kernel +revert

theorem checked159 : ∀ k : Fin (2 ^ free159.length), TransitionCheck 159 (unpackCode free159 k.val) (rows159 k) := by
  decide +kernel +revert

theorem covered (j : Fin 16) : ∀ c : Fin 512,
    Covered (spanCodes (c.val :: frozenWangBasis ⟨144 + j.val, by omega⟩)) := by
  fin_cases j
  · exact extensions_of_normalized 144 free144 normalized144 rows144 checked144
  · exact extensions_of_normalized 145 free145 normalized145 rows145 checked145
  · exact extensions_of_normalized 146 free146 normalized146 rows146 checked146
  · exact extensions_of_normalized 147 free147 normalized147 rows147 checked147
  · exact extensions_of_normalized 148 free148 normalized148 rows148 checked148
  · exact extensions_of_normalized 149 free149 normalized149 rows149 checked149
  · exact extensions_of_normalized 150 free150 normalized150 rows150 checked150
  · exact extensions_of_normalized 151 free151 normalized151 rows151 checked151
  · exact extensions_of_normalized 152 free152 normalized152 rows152 checked152
  · exact extensions_of_normalized 153 free153 normalized153 rows153 checked153
  · exact extensions_of_normalized 154 free154 normalized154 rows154 checked154
  · exact extensions_of_normalized 155 free155 normalized155 rows155 checked155
  · exact extensions_of_normalized 156 free156 normalized156 rows156 checked156
  · exact extensions_of_normalized 157 free157 normalized157 rows157 checked157
  · exact extensions_of_normalized 158 free158 normalized158 rows158 checked158
  · exact extensions_of_normalized 159 free159 normalized159 rows159 checked159

end QiushiMatmul.GlobalOrbit.Cases9
