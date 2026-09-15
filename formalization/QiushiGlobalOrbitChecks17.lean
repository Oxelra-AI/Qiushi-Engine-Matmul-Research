import QiushiGlobalOrbitData17

namespace QiushiMatmul.GlobalOrbit.Cases17
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem normalized272 : NormalizationCheck (frozenWangBasis 272) free272 := by
  decide +kernel +revert

theorem checked272 : ∀ k : Fin (2 ^ free272.length), TransitionCheck 272 (unpackCode free272 k.val) (rows272 k) := by
  decide +kernel +revert

theorem normalized273 : NormalizationCheck (frozenWangBasis 273) free273 := by
  decide +kernel +revert

theorem checked273 : ∀ k : Fin (2 ^ free273.length), TransitionCheck 273 (unpackCode free273 k.val) (rows273 k) := by
  decide +kernel +revert

theorem normalized274 : NormalizationCheck (frozenWangBasis 274) free274 := by
  decide +kernel +revert

theorem checked274 : ∀ k : Fin (2 ^ free274.length), TransitionCheck 274 (unpackCode free274 k.val) (rows274 k) := by
  decide +kernel +revert

theorem normalized275 : NormalizationCheck (frozenWangBasis 275) free275 := by
  decide +kernel +revert

theorem checked275 : ∀ k : Fin (2 ^ free275.length), TransitionCheck 275 (unpackCode free275 k.val) (rows275 k) := by
  decide +kernel +revert

theorem normalized276 : NormalizationCheck (frozenWangBasis 276) free276 := by
  decide +kernel +revert

theorem checked276 : ∀ k : Fin (2 ^ free276.length), TransitionCheck 276 (unpackCode free276 k.val) (rows276 k) := by
  decide +kernel +revert

theorem normalized277 : NormalizationCheck (frozenWangBasis 277) free277 := by
  decide +kernel +revert

theorem checked277 : ∀ k : Fin (2 ^ free277.length), TransitionCheck 277 (unpackCode free277 k.val) (rows277 k) := by
  decide +kernel +revert

theorem normalized278 : NormalizationCheck (frozenWangBasis 278) free278 := by
  decide +kernel +revert

theorem checked278 : ∀ k : Fin (2 ^ free278.length), TransitionCheck 278 (unpackCode free278 k.val) (rows278 k) := by
  decide +kernel +revert

theorem normalized279 : NormalizationCheck (frozenWangBasis 279) free279 := by
  decide +kernel +revert

theorem checked279 : ∀ k : Fin (2 ^ free279.length), TransitionCheck 279 (unpackCode free279 k.val) (rows279 k) := by
  decide +kernel +revert

theorem normalized280 : NormalizationCheck (frozenWangBasis 280) free280 := by
  decide +kernel +revert

theorem checked280 : ∀ k : Fin (2 ^ free280.length), TransitionCheck 280 (unpackCode free280 k.val) (rows280 k) := by
  decide +kernel +revert

theorem normalized281 : NormalizationCheck (frozenWangBasis 281) free281 := by
  decide +kernel +revert

theorem checked281 : ∀ k : Fin (2 ^ free281.length), TransitionCheck 281 (unpackCode free281 k.val) (rows281 k) := by
  decide +kernel +revert

theorem normalized282 : NormalizationCheck (frozenWangBasis 282) free282 := by
  decide +kernel +revert

theorem checked282 : ∀ k : Fin (2 ^ free282.length), TransitionCheck 282 (unpackCode free282 k.val) (rows282 k) := by
  decide +kernel +revert

theorem normalized283 : NormalizationCheck (frozenWangBasis 283) free283 := by
  decide +kernel +revert

theorem checked283 : ∀ k : Fin (2 ^ free283.length), TransitionCheck 283 (unpackCode free283 k.val) (rows283 k) := by
  decide +kernel +revert

theorem normalized284 : NormalizationCheck (frozenWangBasis 284) free284 := by
  decide +kernel +revert

theorem checked284 : ∀ k : Fin (2 ^ free284.length), TransitionCheck 284 (unpackCode free284 k.val) (rows284 k) := by
  decide +kernel +revert

theorem normalized285 : NormalizationCheck (frozenWangBasis 285) free285 := by
  decide +kernel +revert

theorem checked285 : ∀ k : Fin (2 ^ free285.length), TransitionCheck 285 (unpackCode free285 k.val) (rows285 k) := by
  decide +kernel +revert

theorem normalized286 : NormalizationCheck (frozenWangBasis 286) free286 := by
  decide +kernel +revert

theorem checked286 : ∀ k : Fin (2 ^ free286.length), TransitionCheck 286 (unpackCode free286 k.val) (rows286 k) := by
  decide +kernel +revert

theorem normalized287 : NormalizationCheck (frozenWangBasis 287) free287 := by
  decide +kernel +revert

theorem checked287 : ∀ k : Fin (2 ^ free287.length), TransitionCheck 287 (unpackCode free287 k.val) (rows287 k) := by
  decide +kernel +revert

theorem covered (j : Fin 16) : ∀ c : Fin 512,
    Covered (spanCodes (c.val :: frozenWangBasis ⟨272 + j.val, by omega⟩)) := by
  fin_cases j
  · exact extensions_of_normalized 272 free272 normalized272 rows272 checked272
  · exact extensions_of_normalized 273 free273 normalized273 rows273 checked273
  · exact extensions_of_normalized 274 free274 normalized274 rows274 checked274
  · exact extensions_of_normalized 275 free275 normalized275 rows275 checked275
  · exact extensions_of_normalized 276 free276 normalized276 rows276 checked276
  · exact extensions_of_normalized 277 free277 normalized277 rows277 checked277
  · exact extensions_of_normalized 278 free278 normalized278 rows278 checked278
  · exact extensions_of_normalized 279 free279 normalized279 rows279 checked279
  · exact extensions_of_normalized 280 free280 normalized280 rows280 checked280
  · exact extensions_of_normalized 281 free281 normalized281 rows281 checked281
  · exact extensions_of_normalized 282 free282 normalized282 rows282 checked282
  · exact extensions_of_normalized 283 free283 normalized283 rows283 checked283
  · exact extensions_of_normalized 284 free284 normalized284 rows284 checked284
  · exact extensions_of_normalized 285 free285 normalized285 rows285 checked285
  · exact extensions_of_normalized 286 free286 normalized286 rows286 checked286
  · exact extensions_of_normalized 287 free287 normalized287 rows287 checked287

end QiushiMatmul.GlobalOrbit.Cases17
