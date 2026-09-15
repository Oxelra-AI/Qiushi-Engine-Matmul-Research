import QiushiGlobalOrbitData21

namespace QiushiMatmul.GlobalOrbit.Cases21
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem normalized336 : NormalizationCheck (frozenWangBasis 336) free336 := by
  decide +kernel +revert

theorem checked336 : ∀ k : Fin (2 ^ free336.length), TransitionCheck 336 (unpackCode free336 k.val) (rows336 k) := by
  decide +kernel +revert

theorem normalized337 : NormalizationCheck (frozenWangBasis 337) free337 := by
  decide +kernel +revert

theorem checked337 : ∀ k : Fin (2 ^ free337.length), TransitionCheck 337 (unpackCode free337 k.val) (rows337 k) := by
  decide +kernel +revert

theorem normalized338 : NormalizationCheck (frozenWangBasis 338) free338 := by
  decide +kernel +revert

theorem checked338 : ∀ k : Fin (2 ^ free338.length), TransitionCheck 338 (unpackCode free338 k.val) (rows338 k) := by
  decide +kernel +revert

theorem normalized339 : NormalizationCheck (frozenWangBasis 339) free339 := by
  decide +kernel +revert

theorem checked339 : ∀ k : Fin (2 ^ free339.length), TransitionCheck 339 (unpackCode free339 k.val) (rows339 k) := by
  decide +kernel +revert

theorem normalized340 : NormalizationCheck (frozenWangBasis 340) free340 := by
  decide +kernel +revert

theorem checked340 : ∀ k : Fin (2 ^ free340.length), TransitionCheck 340 (unpackCode free340 k.val) (rows340 k) := by
  decide +kernel +revert

theorem normalized341 : NormalizationCheck (frozenWangBasis 341) free341 := by
  decide +kernel +revert

theorem checked341 : ∀ k : Fin (2 ^ free341.length), TransitionCheck 341 (unpackCode free341 k.val) (rows341 k) := by
  decide +kernel +revert

theorem normalized342 : NormalizationCheck (frozenWangBasis 342) free342 := by
  decide +kernel +revert

theorem checked342 : ∀ k : Fin (2 ^ free342.length), TransitionCheck 342 (unpackCode free342 k.val) (rows342 k) := by
  decide +kernel +revert

theorem normalized343 : NormalizationCheck (frozenWangBasis 343) free343 := by
  decide +kernel +revert

theorem checked343 : ∀ k : Fin (2 ^ free343.length), TransitionCheck 343 (unpackCode free343 k.val) (rows343 k) := by
  decide +kernel +revert

theorem normalized344 : NormalizationCheck (frozenWangBasis 344) free344 := by
  decide +kernel +revert

theorem checked344 : ∀ k : Fin (2 ^ free344.length), TransitionCheck 344 (unpackCode free344 k.val) (rows344 k) := by
  decide +kernel +revert

theorem normalized345 : NormalizationCheck (frozenWangBasis 345) free345 := by
  decide +kernel +revert

theorem checked345 : ∀ k : Fin (2 ^ free345.length), TransitionCheck 345 (unpackCode free345 k.val) (rows345 k) := by
  decide +kernel +revert

theorem normalized346 : NormalizationCheck (frozenWangBasis 346) free346 := by
  decide +kernel +revert

theorem checked346 : ∀ k : Fin (2 ^ free346.length), TransitionCheck 346 (unpackCode free346 k.val) (rows346 k) := by
  decide +kernel +revert

theorem normalized347 : NormalizationCheck (frozenWangBasis 347) free347 := by
  decide +kernel +revert

theorem checked347 : ∀ k : Fin (2 ^ free347.length), TransitionCheck 347 (unpackCode free347 k.val) (rows347 k) := by
  decide +kernel +revert

theorem normalized348 : NormalizationCheck (frozenWangBasis 348) free348 := by
  decide +kernel +revert

theorem checked348 : ∀ k : Fin (2 ^ free348.length), TransitionCheck 348 (unpackCode free348 k.val) (rows348 k) := by
  decide +kernel +revert

theorem normalized349 : NormalizationCheck (frozenWangBasis 349) free349 := by
  decide +kernel +revert

theorem checked349 : ∀ k : Fin (2 ^ free349.length), TransitionCheck 349 (unpackCode free349 k.val) (rows349 k) := by
  decide +kernel +revert

theorem normalized350 : NormalizationCheck (frozenWangBasis 350) free350 := by
  decide +kernel +revert

theorem checked350 : ∀ k : Fin (2 ^ free350.length), TransitionCheck 350 (unpackCode free350 k.val) (rows350 k) := by
  decide +kernel +revert

theorem normalized351 : NormalizationCheck (frozenWangBasis 351) free351 := by
  decide +kernel +revert

theorem checked351 : ∀ k : Fin (2 ^ free351.length), TransitionCheck 351 (unpackCode free351 k.val) (rows351 k) := by
  decide +kernel +revert

theorem covered (j : Fin 16) : ∀ c : Fin 512,
    Covered (spanCodes (c.val :: frozenWangBasis ⟨336 + j.val, by omega⟩)) := by
  fin_cases j
  · exact extensions_of_normalized 336 free336 normalized336 rows336 checked336
  · exact extensions_of_normalized 337 free337 normalized337 rows337 checked337
  · exact extensions_of_normalized 338 free338 normalized338 rows338 checked338
  · exact extensions_of_normalized 339 free339 normalized339 rows339 checked339
  · exact extensions_of_normalized 340 free340 normalized340 rows340 checked340
  · exact extensions_of_normalized 341 free341 normalized341 rows341 checked341
  · exact extensions_of_normalized 342 free342 normalized342 rows342 checked342
  · exact extensions_of_normalized 343 free343 normalized343 rows343 checked343
  · exact extensions_of_normalized 344 free344 normalized344 rows344 checked344
  · exact extensions_of_normalized 345 free345 normalized345 rows345 checked345
  · exact extensions_of_normalized 346 free346 normalized346 rows346 checked346
  · exact extensions_of_normalized 347 free347 normalized347 rows347 checked347
  · exact extensions_of_normalized 348 free348 normalized348 rows348 checked348
  · exact extensions_of_normalized 349 free349 normalized349 rows349 checked349
  · exact extensions_of_normalized 350 free350 normalized350 rows350 checked350
  · exact extensions_of_normalized 351 free351 normalized351 rows351 checked351

end QiushiMatmul.GlobalOrbit.Cases21
