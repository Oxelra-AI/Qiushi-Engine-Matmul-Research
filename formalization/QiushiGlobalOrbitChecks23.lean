import QiushiGlobalOrbitData23

namespace QiushiMatmul.GlobalOrbit.Cases23
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem normalized368 : NormalizationCheck (frozenWangBasis 368) free368 := by
  decide +kernel +revert

theorem checked368 : ∀ k : Fin (2 ^ free368.length), TransitionCheck 368 (unpackCode free368 k.val) (rows368 k) := by
  decide +kernel +revert

theorem normalized369 : NormalizationCheck (frozenWangBasis 369) free369 := by
  decide +kernel +revert

theorem checked369 : ∀ k : Fin (2 ^ free369.length), TransitionCheck 369 (unpackCode free369 k.val) (rows369 k) := by
  decide +kernel +revert

theorem normalized370 : NormalizationCheck (frozenWangBasis 370) free370 := by
  decide +kernel +revert

theorem checked370 : ∀ k : Fin (2 ^ free370.length), TransitionCheck 370 (unpackCode free370 k.val) (rows370 k) := by
  decide +kernel +revert

theorem normalized371 : NormalizationCheck (frozenWangBasis 371) free371 := by
  decide +kernel +revert

theorem checked371 : ∀ k : Fin (2 ^ free371.length), TransitionCheck 371 (unpackCode free371 k.val) (rows371 k) := by
  decide +kernel +revert

theorem normalized372 : NormalizationCheck (frozenWangBasis 372) free372 := by
  decide +kernel +revert

theorem checked372 : ∀ k : Fin (2 ^ free372.length), TransitionCheck 372 (unpackCode free372 k.val) (rows372 k) := by
  decide +kernel +revert

theorem normalized373 : NormalizationCheck (frozenWangBasis 373) free373 := by
  decide +kernel +revert

theorem checked373 : ∀ k : Fin (2 ^ free373.length), TransitionCheck 373 (unpackCode free373 k.val) (rows373 k) := by
  decide +kernel +revert

theorem normalized374 : NormalizationCheck (frozenWangBasis 374) free374 := by
  decide +kernel +revert

theorem checked374 : ∀ k : Fin (2 ^ free374.length), TransitionCheck 374 (unpackCode free374 k.val) (rows374 k) := by
  decide +kernel +revert

theorem normalized375 : NormalizationCheck (frozenWangBasis 375) free375 := by
  decide +kernel +revert

theorem checked375 : ∀ k : Fin (2 ^ free375.length), TransitionCheck 375 (unpackCode free375 k.val) (rows375 k) := by
  decide +kernel +revert

theorem normalized376 : NormalizationCheck (frozenWangBasis 376) free376 := by
  decide +kernel +revert

theorem checked376 : ∀ k : Fin (2 ^ free376.length), TransitionCheck 376 (unpackCode free376 k.val) (rows376 k) := by
  decide +kernel +revert

theorem normalized377 : NormalizationCheck (frozenWangBasis 377) free377 := by
  decide +kernel +revert

theorem checked377 : ∀ k : Fin (2 ^ free377.length), TransitionCheck 377 (unpackCode free377 k.val) (rows377 k) := by
  decide +kernel +revert

theorem normalized378 : NormalizationCheck (frozenWangBasis 378) free378 := by
  decide +kernel +revert

theorem checked378 : ∀ k : Fin (2 ^ free378.length), TransitionCheck 378 (unpackCode free378 k.val) (rows378 k) := by
  decide +kernel +revert

theorem normalized379 : NormalizationCheck (frozenWangBasis 379) free379 := by
  decide +kernel +revert

theorem checked379 : ∀ k : Fin (2 ^ free379.length), TransitionCheck 379 (unpackCode free379 k.val) (rows379 k) := by
  decide +kernel +revert

theorem normalized380 : NormalizationCheck (frozenWangBasis 380) free380 := by
  decide +kernel +revert

theorem checked380 : ∀ k : Fin (2 ^ free380.length), TransitionCheck 380 (unpackCode free380 k.val) (rows380 k) := by
  decide +kernel +revert

theorem normalized381 : NormalizationCheck (frozenWangBasis 381) free381 := by
  decide +kernel +revert

theorem checked381 : ∀ k : Fin (2 ^ free381.length), TransitionCheck 381 (unpackCode free381 k.val) (rows381 k) := by
  decide +kernel +revert

theorem normalized382 : NormalizationCheck (frozenWangBasis 382) free382 := by
  decide +kernel +revert

theorem checked382 : ∀ k : Fin (2 ^ free382.length), TransitionCheck 382 (unpackCode free382 k.val) (rows382 k) := by
  decide +kernel +revert

theorem normalized383 : NormalizationCheck (frozenWangBasis 383) free383 := by
  decide +kernel +revert

theorem checked383 : ∀ k : Fin (2 ^ free383.length), TransitionCheck 383 (unpackCode free383 k.val) (rows383 k) := by
  decide +kernel +revert

theorem covered (j : Fin 16) : ∀ c : Fin 512,
    Covered (spanCodes (c.val :: frozenWangBasis ⟨368 + j.val, by omega⟩)) := by
  fin_cases j
  · exact extensions_of_normalized 368 free368 normalized368 rows368 checked368
  · exact extensions_of_normalized 369 free369 normalized369 rows369 checked369
  · exact extensions_of_normalized 370 free370 normalized370 rows370 checked370
  · exact extensions_of_normalized 371 free371 normalized371 rows371 checked371
  · exact extensions_of_normalized 372 free372 normalized372 rows372 checked372
  · exact extensions_of_normalized 373 free373 normalized373 rows373 checked373
  · exact extensions_of_normalized 374 free374 normalized374 rows374 checked374
  · exact extensions_of_normalized 375 free375 normalized375 rows375 checked375
  · exact extensions_of_normalized 376 free376 normalized376 rows376 checked376
  · exact extensions_of_normalized 377 free377 normalized377 rows377 checked377
  · exact extensions_of_normalized 378 free378 normalized378 rows378 checked378
  · exact extensions_of_normalized 379 free379 normalized379 rows379 checked379
  · exact extensions_of_normalized 380 free380 normalized380 rows380 checked380
  · exact extensions_of_normalized 381 free381 normalized381 rows381 checked381
  · exact extensions_of_normalized 382 free382 normalized382 rows382 checked382
  · exact extensions_of_normalized 383 free383 normalized383 rows383 checked383

end QiushiMatmul.GlobalOrbit.Cases23
