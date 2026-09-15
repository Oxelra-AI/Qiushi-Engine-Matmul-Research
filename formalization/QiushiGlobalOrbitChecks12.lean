import QiushiGlobalOrbitData12

namespace QiushiMatmul.GlobalOrbit.Cases12
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem normalized192 : NormalizationCheck (frozenWangBasis 192) free192 := by
  decide +kernel +revert

theorem checked192 : ∀ k : Fin (2 ^ free192.length), TransitionCheck 192 (unpackCode free192 k.val) (rows192 k) := by
  decide +kernel +revert

theorem normalized193 : NormalizationCheck (frozenWangBasis 193) free193 := by
  decide +kernel +revert

theorem checked193 : ∀ k : Fin (2 ^ free193.length), TransitionCheck 193 (unpackCode free193 k.val) (rows193 k) := by
  decide +kernel +revert

theorem normalized194 : NormalizationCheck (frozenWangBasis 194) free194 := by
  decide +kernel +revert

theorem checked194 : ∀ k : Fin (2 ^ free194.length), TransitionCheck 194 (unpackCode free194 k.val) (rows194 k) := by
  decide +kernel +revert

theorem normalized195 : NormalizationCheck (frozenWangBasis 195) free195 := by
  decide +kernel +revert

theorem checked195 : ∀ k : Fin (2 ^ free195.length), TransitionCheck 195 (unpackCode free195 k.val) (rows195 k) := by
  decide +kernel +revert

theorem normalized196 : NormalizationCheck (frozenWangBasis 196) free196 := by
  decide +kernel +revert

theorem checked196 : ∀ k : Fin (2 ^ free196.length), TransitionCheck 196 (unpackCode free196 k.val) (rows196 k) := by
  decide +kernel +revert

theorem normalized197 : NormalizationCheck (frozenWangBasis 197) free197 := by
  decide +kernel +revert

theorem checked197 : ∀ k : Fin (2 ^ free197.length), TransitionCheck 197 (unpackCode free197 k.val) (rows197 k) := by
  decide +kernel +revert

theorem normalized198 : NormalizationCheck (frozenWangBasis 198) free198 := by
  decide +kernel +revert

theorem checked198 : ∀ k : Fin (2 ^ free198.length), TransitionCheck 198 (unpackCode free198 k.val) (rows198 k) := by
  decide +kernel +revert

theorem normalized199 : NormalizationCheck (frozenWangBasis 199) free199 := by
  decide +kernel +revert

theorem checked199 : ∀ k : Fin (2 ^ free199.length), TransitionCheck 199 (unpackCode free199 k.val) (rows199 k) := by
  decide +kernel +revert

theorem normalized200 : NormalizationCheck (frozenWangBasis 200) free200 := by
  decide +kernel +revert

theorem checked200 : ∀ k : Fin (2 ^ free200.length), TransitionCheck 200 (unpackCode free200 k.val) (rows200 k) := by
  decide +kernel +revert

theorem normalized201 : NormalizationCheck (frozenWangBasis 201) free201 := by
  decide +kernel +revert

theorem checked201 : ∀ k : Fin (2 ^ free201.length), TransitionCheck 201 (unpackCode free201 k.val) (rows201 k) := by
  decide +kernel +revert

theorem normalized202 : NormalizationCheck (frozenWangBasis 202) free202 := by
  decide +kernel +revert

theorem checked202 : ∀ k : Fin (2 ^ free202.length), TransitionCheck 202 (unpackCode free202 k.val) (rows202 k) := by
  decide +kernel +revert

theorem normalized203 : NormalizationCheck (frozenWangBasis 203) free203 := by
  decide +kernel +revert

theorem checked203 : ∀ k : Fin (2 ^ free203.length), TransitionCheck 203 (unpackCode free203 k.val) (rows203 k) := by
  decide +kernel +revert

theorem normalized204 : NormalizationCheck (frozenWangBasis 204) free204 := by
  decide +kernel +revert

theorem checked204 : ∀ k : Fin (2 ^ free204.length), TransitionCheck 204 (unpackCode free204 k.val) (rows204 k) := by
  decide +kernel +revert

theorem normalized205 : NormalizationCheck (frozenWangBasis 205) free205 := by
  decide +kernel +revert

theorem checked205 : ∀ k : Fin (2 ^ free205.length), TransitionCheck 205 (unpackCode free205 k.val) (rows205 k) := by
  decide +kernel +revert

theorem normalized206 : NormalizationCheck (frozenWangBasis 206) free206 := by
  decide +kernel +revert

theorem checked206 : ∀ k : Fin (2 ^ free206.length), TransitionCheck 206 (unpackCode free206 k.val) (rows206 k) := by
  decide +kernel +revert

theorem normalized207 : NormalizationCheck (frozenWangBasis 207) free207 := by
  decide +kernel +revert

theorem checked207 : ∀ k : Fin (2 ^ free207.length), TransitionCheck 207 (unpackCode free207 k.val) (rows207 k) := by
  decide +kernel +revert

theorem covered (j : Fin 16) : ∀ c : Fin 512,
    Covered (spanCodes (c.val :: frozenWangBasis ⟨192 + j.val, by omega⟩)) := by
  fin_cases j
  · exact extensions_of_normalized 192 free192 normalized192 rows192 checked192
  · exact extensions_of_normalized 193 free193 normalized193 rows193 checked193
  · exact extensions_of_normalized 194 free194 normalized194 rows194 checked194
  · exact extensions_of_normalized 195 free195 normalized195 rows195 checked195
  · exact extensions_of_normalized 196 free196 normalized196 rows196 checked196
  · exact extensions_of_normalized 197 free197 normalized197 rows197 checked197
  · exact extensions_of_normalized 198 free198 normalized198 rows198 checked198
  · exact extensions_of_normalized 199 free199 normalized199 rows199 checked199
  · exact extensions_of_normalized 200 free200 normalized200 rows200 checked200
  · exact extensions_of_normalized 201 free201 normalized201 rows201 checked201
  · exact extensions_of_normalized 202 free202 normalized202 rows202 checked202
  · exact extensions_of_normalized 203 free203 normalized203 rows203 checked203
  · exact extensions_of_normalized 204 free204 normalized204 rows204 checked204
  · exact extensions_of_normalized 205 free205 normalized205 rows205 checked205
  · exact extensions_of_normalized 206 free206 normalized206 rows206 checked206
  · exact extensions_of_normalized 207 free207 normalized207 rows207 checked207

end QiushiMatmul.GlobalOrbit.Cases12
