import QiushiGlobalOrbitData22

namespace QiushiMatmul.GlobalOrbit.Cases22
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem normalized352 : NormalizationCheck (frozenWangBasis 352) free352 := by
  decide +kernel +revert

theorem checked352 : ∀ k : Fin (2 ^ free352.length), TransitionCheck 352 (unpackCode free352 k.val) (rows352 k) := by
  decide +kernel +revert

theorem normalized353 : NormalizationCheck (frozenWangBasis 353) free353 := by
  decide +kernel +revert

theorem checked353 : ∀ k : Fin (2 ^ free353.length), TransitionCheck 353 (unpackCode free353 k.val) (rows353 k) := by
  decide +kernel +revert

theorem normalized354 : NormalizationCheck (frozenWangBasis 354) free354 := by
  decide +kernel +revert

theorem checked354 : ∀ k : Fin (2 ^ free354.length), TransitionCheck 354 (unpackCode free354 k.val) (rows354 k) := by
  decide +kernel +revert

theorem normalized355 : NormalizationCheck (frozenWangBasis 355) free355 := by
  decide +kernel +revert

theorem checked355 : ∀ k : Fin (2 ^ free355.length), TransitionCheck 355 (unpackCode free355 k.val) (rows355 k) := by
  decide +kernel +revert

theorem normalized356 : NormalizationCheck (frozenWangBasis 356) free356 := by
  decide +kernel +revert

theorem checked356 : ∀ k : Fin (2 ^ free356.length), TransitionCheck 356 (unpackCode free356 k.val) (rows356 k) := by
  decide +kernel +revert

theorem normalized357 : NormalizationCheck (frozenWangBasis 357) free357 := by
  decide +kernel +revert

theorem checked357 : ∀ k : Fin (2 ^ free357.length), TransitionCheck 357 (unpackCode free357 k.val) (rows357 k) := by
  decide +kernel +revert

theorem normalized358 : NormalizationCheck (frozenWangBasis 358) free358 := by
  decide +kernel +revert

theorem checked358 : ∀ k : Fin (2 ^ free358.length), TransitionCheck 358 (unpackCode free358 k.val) (rows358 k) := by
  decide +kernel +revert

theorem normalized359 : NormalizationCheck (frozenWangBasis 359) free359 := by
  decide +kernel +revert

theorem checked359 : ∀ k : Fin (2 ^ free359.length), TransitionCheck 359 (unpackCode free359 k.val) (rows359 k) := by
  decide +kernel +revert

theorem normalized360 : NormalizationCheck (frozenWangBasis 360) free360 := by
  decide +kernel +revert

theorem checked360 : ∀ k : Fin (2 ^ free360.length), TransitionCheck 360 (unpackCode free360 k.val) (rows360 k) := by
  decide +kernel +revert

theorem normalized361 : NormalizationCheck (frozenWangBasis 361) free361 := by
  decide +kernel +revert

theorem checked361 : ∀ k : Fin (2 ^ free361.length), TransitionCheck 361 (unpackCode free361 k.val) (rows361 k) := by
  decide +kernel +revert

theorem normalized362 : NormalizationCheck (frozenWangBasis 362) free362 := by
  decide +kernel +revert

theorem checked362 : ∀ k : Fin (2 ^ free362.length), TransitionCheck 362 (unpackCode free362 k.val) (rows362 k) := by
  decide +kernel +revert

theorem normalized363 : NormalizationCheck (frozenWangBasis 363) free363 := by
  decide +kernel +revert

theorem checked363 : ∀ k : Fin (2 ^ free363.length), TransitionCheck 363 (unpackCode free363 k.val) (rows363 k) := by
  decide +kernel +revert

theorem normalized364 : NormalizationCheck (frozenWangBasis 364) free364 := by
  decide +kernel +revert

theorem checked364 : ∀ k : Fin (2 ^ free364.length), TransitionCheck 364 (unpackCode free364 k.val) (rows364 k) := by
  decide +kernel +revert

theorem normalized365 : NormalizationCheck (frozenWangBasis 365) free365 := by
  decide +kernel +revert

theorem checked365 : ∀ k : Fin (2 ^ free365.length), TransitionCheck 365 (unpackCode free365 k.val) (rows365 k) := by
  decide +kernel +revert

theorem normalized366 : NormalizationCheck (frozenWangBasis 366) free366 := by
  decide +kernel +revert

theorem checked366 : ∀ k : Fin (2 ^ free366.length), TransitionCheck 366 (unpackCode free366 k.val) (rows366 k) := by
  decide +kernel +revert

theorem normalized367 : NormalizationCheck (frozenWangBasis 367) free367 := by
  decide +kernel +revert

theorem checked367 : ∀ k : Fin (2 ^ free367.length), TransitionCheck 367 (unpackCode free367 k.val) (rows367 k) := by
  decide +kernel +revert

theorem covered (j : Fin 16) : ∀ c : Fin 512,
    Covered (spanCodes (c.val :: frozenWangBasis ⟨352 + j.val, by omega⟩)) := by
  fin_cases j
  · exact extensions_of_normalized 352 free352 normalized352 rows352 checked352
  · exact extensions_of_normalized 353 free353 normalized353 rows353 checked353
  · exact extensions_of_normalized 354 free354 normalized354 rows354 checked354
  · exact extensions_of_normalized 355 free355 normalized355 rows355 checked355
  · exact extensions_of_normalized 356 free356 normalized356 rows356 checked356
  · exact extensions_of_normalized 357 free357 normalized357 rows357 checked357
  · exact extensions_of_normalized 358 free358 normalized358 rows358 checked358
  · exact extensions_of_normalized 359 free359 normalized359 rows359 checked359
  · exact extensions_of_normalized 360 free360 normalized360 rows360 checked360
  · exact extensions_of_normalized 361 free361 normalized361 rows361 checked361
  · exact extensions_of_normalized 362 free362 normalized362 rows362 checked362
  · exact extensions_of_normalized 363 free363 normalized363 rows363 checked363
  · exact extensions_of_normalized 364 free364 normalized364 rows364 checked364
  · exact extensions_of_normalized 365 free365 normalized365 rows365 checked365
  · exact extensions_of_normalized 366 free366 normalized366 rows366 checked366
  · exact extensions_of_normalized 367 free367 normalized367 rows367 checked367

end QiushiMatmul.GlobalOrbit.Cases22
