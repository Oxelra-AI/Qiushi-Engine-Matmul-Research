import QiushiGlobalOrbitData24

namespace QiushiMatmul.GlobalOrbit.Cases24
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem normalized384 : NormalizationCheck (frozenWangBasis 384) free384 := by
  decide +kernel +revert

theorem checked384 : ∀ k : Fin (2 ^ free384.length), TransitionCheck 384 (unpackCode free384 k.val) (rows384 k) := by
  decide +kernel +revert

theorem normalized385 : NormalizationCheck (frozenWangBasis 385) free385 := by
  decide +kernel +revert

theorem checked385 : ∀ k : Fin (2 ^ free385.length), TransitionCheck 385 (unpackCode free385 k.val) (rows385 k) := by
  decide +kernel +revert

theorem normalized386 : NormalizationCheck (frozenWangBasis 386) free386 := by
  decide +kernel +revert

theorem checked386 : ∀ k : Fin (2 ^ free386.length), TransitionCheck 386 (unpackCode free386 k.val) (rows386 k) := by
  decide +kernel +revert

theorem normalized387 : NormalizationCheck (frozenWangBasis 387) free387 := by
  decide +kernel +revert

theorem checked387 : ∀ k : Fin (2 ^ free387.length), TransitionCheck 387 (unpackCode free387 k.val) (rows387 k) := by
  decide +kernel +revert

theorem normalized388 : NormalizationCheck (frozenWangBasis 388) free388 := by
  decide +kernel +revert

theorem checked388 : ∀ k : Fin (2 ^ free388.length), TransitionCheck 388 (unpackCode free388 k.val) (rows388 k) := by
  decide +kernel +revert

theorem normalized389 : NormalizationCheck (frozenWangBasis 389) free389 := by
  decide +kernel +revert

theorem checked389 : ∀ k : Fin (2 ^ free389.length), TransitionCheck 389 (unpackCode free389 k.val) (rows389 k) := by
  decide +kernel +revert

theorem normalized390 : NormalizationCheck (frozenWangBasis 390) free390 := by
  decide +kernel +revert

theorem checked390 : ∀ k : Fin (2 ^ free390.length), TransitionCheck 390 (unpackCode free390 k.val) (rows390 k) := by
  decide +kernel +revert

theorem normalized391 : NormalizationCheck (frozenWangBasis 391) free391 := by
  decide +kernel +revert

theorem checked391 : ∀ k : Fin (2 ^ free391.length), TransitionCheck 391 (unpackCode free391 k.val) (rows391 k) := by
  decide +kernel +revert

theorem normalized392 : NormalizationCheck (frozenWangBasis 392) free392 := by
  decide +kernel +revert

theorem checked392 : ∀ k : Fin (2 ^ free392.length), TransitionCheck 392 (unpackCode free392 k.val) (rows392 k) := by
  decide +kernel +revert

theorem normalized393 : NormalizationCheck (frozenWangBasis 393) free393 := by
  decide +kernel +revert

theorem checked393 : ∀ k : Fin (2 ^ free393.length), TransitionCheck 393 (unpackCode free393 k.val) (rows393 k) := by
  decide +kernel +revert

theorem normalized394 : NormalizationCheck (frozenWangBasis 394) free394 := by
  decide +kernel +revert

theorem checked394 : ∀ k : Fin (2 ^ free394.length), TransitionCheck 394 (unpackCode free394 k.val) (rows394 k) := by
  decide +kernel +revert

theorem normalized395 : NormalizationCheck (frozenWangBasis 395) free395 := by
  decide +kernel +revert

theorem checked395 : ∀ k : Fin (2 ^ free395.length), TransitionCheck 395 (unpackCode free395 k.val) (rows395 k) := by
  decide +kernel +revert

theorem normalized396 : NormalizationCheck (frozenWangBasis 396) free396 := by
  decide +kernel +revert

theorem checked396 : ∀ k : Fin (2 ^ free396.length), TransitionCheck 396 (unpackCode free396 k.val) (rows396 k) := by
  decide +kernel +revert

theorem normalized397 : NormalizationCheck (frozenWangBasis 397) free397 := by
  decide +kernel +revert

theorem checked397 : ∀ k : Fin (2 ^ free397.length), TransitionCheck 397 (unpackCode free397 k.val) (rows397 k) := by
  decide +kernel +revert

theorem normalized398 : NormalizationCheck (frozenWangBasis 398) free398 := by
  decide +kernel +revert

theorem checked398 : ∀ k : Fin (2 ^ free398.length), TransitionCheck 398 (unpackCode free398 k.val) (rows398 k) := by
  decide +kernel +revert

theorem normalized399 : NormalizationCheck (frozenWangBasis 399) free399 := by
  decide +kernel +revert

theorem checked399 : ∀ k : Fin (2 ^ free399.length), TransitionCheck 399 (unpackCode free399 k.val) (rows399 k) := by
  decide +kernel +revert

theorem covered (j : Fin 16) : ∀ c : Fin 512,
    Covered (spanCodes (c.val :: frozenWangBasis ⟨384 + j.val, by omega⟩)) := by
  fin_cases j
  · exact extensions_of_normalized 384 free384 normalized384 rows384 checked384
  · exact extensions_of_normalized 385 free385 normalized385 rows385 checked385
  · exact extensions_of_normalized 386 free386 normalized386 rows386 checked386
  · exact extensions_of_normalized 387 free387 normalized387 rows387 checked387
  · exact extensions_of_normalized 388 free388 normalized388 rows388 checked388
  · exact extensions_of_normalized 389 free389 normalized389 rows389 checked389
  · exact extensions_of_normalized 390 free390 normalized390 rows390 checked390
  · exact extensions_of_normalized 391 free391 normalized391 rows391 checked391
  · exact extensions_of_normalized 392 free392 normalized392 rows392 checked392
  · exact extensions_of_normalized 393 free393 normalized393 rows393 checked393
  · exact extensions_of_normalized 394 free394 normalized394 rows394 checked394
  · exact extensions_of_normalized 395 free395 normalized395 rows395 checked395
  · exact extensions_of_normalized 396 free396 normalized396 rows396 checked396
  · exact extensions_of_normalized 397 free397 normalized397 rows397 checked397
  · exact extensions_of_normalized 398 free398 normalized398 rows398 checked398
  · exact extensions_of_normalized 399 free399 normalized399 rows399 checked399

end QiushiMatmul.GlobalOrbit.Cases24
