import QiushiGlobalOrbitData14

namespace QiushiMatmul.GlobalOrbit.Cases14
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem normalized224 : NormalizationCheck (frozenWangBasis 224) free224 := by
  decide +kernel +revert

theorem checked224 : ∀ k : Fin (2 ^ free224.length), TransitionCheck 224 (unpackCode free224 k.val) (rows224 k) := by
  decide +kernel +revert

theorem normalized225 : NormalizationCheck (frozenWangBasis 225) free225 := by
  decide +kernel +revert

theorem checked225 : ∀ k : Fin (2 ^ free225.length), TransitionCheck 225 (unpackCode free225 k.val) (rows225 k) := by
  decide +kernel +revert

theorem normalized226 : NormalizationCheck (frozenWangBasis 226) free226 := by
  decide +kernel +revert

theorem checked226 : ∀ k : Fin (2 ^ free226.length), TransitionCheck 226 (unpackCode free226 k.val) (rows226 k) := by
  decide +kernel +revert

theorem normalized227 : NormalizationCheck (frozenWangBasis 227) free227 := by
  decide +kernel +revert

theorem checked227 : ∀ k : Fin (2 ^ free227.length), TransitionCheck 227 (unpackCode free227 k.val) (rows227 k) := by
  decide +kernel +revert

theorem normalized228 : NormalizationCheck (frozenWangBasis 228) free228 := by
  decide +kernel +revert

theorem checked228 : ∀ k : Fin (2 ^ free228.length), TransitionCheck 228 (unpackCode free228 k.val) (rows228 k) := by
  decide +kernel +revert

theorem normalized229 : NormalizationCheck (frozenWangBasis 229) free229 := by
  decide +kernel +revert

theorem checked229 : ∀ k : Fin (2 ^ free229.length), TransitionCheck 229 (unpackCode free229 k.val) (rows229 k) := by
  decide +kernel +revert

theorem normalized230 : NormalizationCheck (frozenWangBasis 230) free230 := by
  decide +kernel +revert

theorem checked230 : ∀ k : Fin (2 ^ free230.length), TransitionCheck 230 (unpackCode free230 k.val) (rows230 k) := by
  decide +kernel +revert

theorem normalized231 : NormalizationCheck (frozenWangBasis 231) free231 := by
  decide +kernel +revert

theorem checked231 : ∀ k : Fin (2 ^ free231.length), TransitionCheck 231 (unpackCode free231 k.val) (rows231 k) := by
  decide +kernel +revert

theorem normalized232 : NormalizationCheck (frozenWangBasis 232) free232 := by
  decide +kernel +revert

theorem checked232 : ∀ k : Fin (2 ^ free232.length), TransitionCheck 232 (unpackCode free232 k.val) (rows232 k) := by
  decide +kernel +revert

theorem normalized233 : NormalizationCheck (frozenWangBasis 233) free233 := by
  decide +kernel +revert

theorem checked233 : ∀ k : Fin (2 ^ free233.length), TransitionCheck 233 (unpackCode free233 k.val) (rows233 k) := by
  decide +kernel +revert

theorem normalized234 : NormalizationCheck (frozenWangBasis 234) free234 := by
  decide +kernel +revert

theorem checked234 : ∀ k : Fin (2 ^ free234.length), TransitionCheck 234 (unpackCode free234 k.val) (rows234 k) := by
  decide +kernel +revert

theorem normalized235 : NormalizationCheck (frozenWangBasis 235) free235 := by
  decide +kernel +revert

theorem checked235 : ∀ k : Fin (2 ^ free235.length), TransitionCheck 235 (unpackCode free235 k.val) (rows235 k) := by
  decide +kernel +revert

theorem normalized236 : NormalizationCheck (frozenWangBasis 236) free236 := by
  decide +kernel +revert

theorem checked236 : ∀ k : Fin (2 ^ free236.length), TransitionCheck 236 (unpackCode free236 k.val) (rows236 k) := by
  decide +kernel +revert

theorem normalized237 : NormalizationCheck (frozenWangBasis 237) free237 := by
  decide +kernel +revert

theorem checked237 : ∀ k : Fin (2 ^ free237.length), TransitionCheck 237 (unpackCode free237 k.val) (rows237 k) := by
  decide +kernel +revert

theorem normalized238 : NormalizationCheck (frozenWangBasis 238) free238 := by
  decide +kernel +revert

theorem checked238 : ∀ k : Fin (2 ^ free238.length), TransitionCheck 238 (unpackCode free238 k.val) (rows238 k) := by
  decide +kernel +revert

theorem normalized239 : NormalizationCheck (frozenWangBasis 239) free239 := by
  decide +kernel +revert

theorem checked239 : ∀ k : Fin (2 ^ free239.length), TransitionCheck 239 (unpackCode free239 k.val) (rows239 k) := by
  decide +kernel +revert

theorem covered (j : Fin 16) : ∀ c : Fin 512,
    Covered (spanCodes (c.val :: frozenWangBasis ⟨224 + j.val, by omega⟩)) := by
  fin_cases j
  · exact extensions_of_normalized 224 free224 normalized224 rows224 checked224
  · exact extensions_of_normalized 225 free225 normalized225 rows225 checked225
  · exact extensions_of_normalized 226 free226 normalized226 rows226 checked226
  · exact extensions_of_normalized 227 free227 normalized227 rows227 checked227
  · exact extensions_of_normalized 228 free228 normalized228 rows228 checked228
  · exact extensions_of_normalized 229 free229 normalized229 rows229 checked229
  · exact extensions_of_normalized 230 free230 normalized230 rows230 checked230
  · exact extensions_of_normalized 231 free231 normalized231 rows231 checked231
  · exact extensions_of_normalized 232 free232 normalized232 rows232 checked232
  · exact extensions_of_normalized 233 free233 normalized233 rows233 checked233
  · exact extensions_of_normalized 234 free234 normalized234 rows234 checked234
  · exact extensions_of_normalized 235 free235 normalized235 rows235 checked235
  · exact extensions_of_normalized 236 free236 normalized236 rows236 checked236
  · exact extensions_of_normalized 237 free237 normalized237 rows237 checked237
  · exact extensions_of_normalized 238 free238 normalized238 rows238 checked238
  · exact extensions_of_normalized 239 free239 normalized239 rows239 checked239

end QiushiMatmul.GlobalOrbit.Cases14
