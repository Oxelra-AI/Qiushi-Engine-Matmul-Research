import QiushiGlobalOrbitData29

namespace QiushiMatmul.GlobalOrbit.Cases29
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem normalized464 : NormalizationCheck (frozenWangBasis 464) free464 := by
  decide +kernel +revert

theorem checked464 : ∀ k : Fin (2 ^ free464.length), TransitionCheck 464 (unpackCode free464 k.val) (rows464 k) := by
  decide +kernel +revert

theorem normalized465 : NormalizationCheck (frozenWangBasis 465) free465 := by
  decide +kernel +revert

theorem checked465 : ∀ k : Fin (2 ^ free465.length), TransitionCheck 465 (unpackCode free465 k.val) (rows465 k) := by
  decide +kernel +revert

theorem normalized466 : NormalizationCheck (frozenWangBasis 466) free466 := by
  decide +kernel +revert

theorem checked466 : ∀ k : Fin (2 ^ free466.length), TransitionCheck 466 (unpackCode free466 k.val) (rows466 k) := by
  decide +kernel +revert

theorem normalized467 : NormalizationCheck (frozenWangBasis 467) free467 := by
  decide +kernel +revert

theorem checked467 : ∀ k : Fin (2 ^ free467.length), TransitionCheck 467 (unpackCode free467 k.val) (rows467 k) := by
  decide +kernel +revert

theorem normalized468 : NormalizationCheck (frozenWangBasis 468) free468 := by
  decide +kernel +revert

theorem checked468 : ∀ k : Fin (2 ^ free468.length), TransitionCheck 468 (unpackCode free468 k.val) (rows468 k) := by
  decide +kernel +revert

theorem normalized469 : NormalizationCheck (frozenWangBasis 469) free469 := by
  decide +kernel +revert

theorem checked469 : ∀ k : Fin (2 ^ free469.length), TransitionCheck 469 (unpackCode free469 k.val) (rows469 k) := by
  decide +kernel +revert

theorem normalized470 : NormalizationCheck (frozenWangBasis 470) free470 := by
  decide +kernel +revert

theorem checked470 : ∀ k : Fin (2 ^ free470.length), TransitionCheck 470 (unpackCode free470 k.val) (rows470 k) := by
  decide +kernel +revert

theorem normalized471 : NormalizationCheck (frozenWangBasis 471) free471 := by
  decide +kernel +revert

theorem checked471 : ∀ k : Fin (2 ^ free471.length), TransitionCheck 471 (unpackCode free471 k.val) (rows471 k) := by
  decide +kernel +revert

theorem normalized472 : NormalizationCheck (frozenWangBasis 472) free472 := by
  decide +kernel +revert

theorem checked472 : ∀ k : Fin (2 ^ free472.length), TransitionCheck 472 (unpackCode free472 k.val) (rows472 k) := by
  decide +kernel +revert

theorem normalized473 : NormalizationCheck (frozenWangBasis 473) free473 := by
  decide +kernel +revert

theorem checked473 : ∀ k : Fin (2 ^ free473.length), TransitionCheck 473 (unpackCode free473 k.val) (rows473 k) := by
  decide +kernel +revert

theorem normalized474 : NormalizationCheck (frozenWangBasis 474) free474 := by
  decide +kernel +revert

theorem checked474 : ∀ k : Fin (2 ^ free474.length), TransitionCheck 474 (unpackCode free474 k.val) (rows474 k) := by
  decide +kernel +revert

theorem normalized475 : NormalizationCheck (frozenWangBasis 475) free475 := by
  decide +kernel +revert

theorem checked475 : ∀ k : Fin (2 ^ free475.length), TransitionCheck 475 (unpackCode free475 k.val) (rows475 k) := by
  decide +kernel +revert

theorem normalized476 : NormalizationCheck (frozenWangBasis 476) free476 := by
  decide +kernel +revert

theorem checked476 : ∀ k : Fin (2 ^ free476.length), TransitionCheck 476 (unpackCode free476 k.val) (rows476 k) := by
  decide +kernel +revert

theorem normalized477 : NormalizationCheck (frozenWangBasis 477) free477 := by
  decide +kernel +revert

theorem checked477 : ∀ k : Fin (2 ^ free477.length), TransitionCheck 477 (unpackCode free477 k.val) (rows477 k) := by
  decide +kernel +revert

theorem normalized478 : NormalizationCheck (frozenWangBasis 478) free478 := by
  decide +kernel +revert

theorem checked478 : ∀ k : Fin (2 ^ free478.length), TransitionCheck 478 (unpackCode free478 k.val) (rows478 k) := by
  decide +kernel +revert

theorem normalized479 : NormalizationCheck (frozenWangBasis 479) free479 := by
  decide +kernel +revert

theorem checked479 : ∀ k : Fin (2 ^ free479.length), TransitionCheck 479 (unpackCode free479 k.val) (rows479 k) := by
  decide +kernel +revert

theorem covered (j : Fin 16) : ∀ c : Fin 512,
    Covered (spanCodes (c.val :: frozenWangBasis ⟨464 + j.val, by omega⟩)) := by
  fin_cases j
  · exact extensions_of_normalized 464 free464 normalized464 rows464 checked464
  · exact extensions_of_normalized 465 free465 normalized465 rows465 checked465
  · exact extensions_of_normalized 466 free466 normalized466 rows466 checked466
  · exact extensions_of_normalized 467 free467 normalized467 rows467 checked467
  · exact extensions_of_normalized 468 free468 normalized468 rows468 checked468
  · exact extensions_of_normalized 469 free469 normalized469 rows469 checked469
  · exact extensions_of_normalized 470 free470 normalized470 rows470 checked470
  · exact extensions_of_normalized 471 free471 normalized471 rows471 checked471
  · exact extensions_of_normalized 472 free472 normalized472 rows472 checked472
  · exact extensions_of_normalized 473 free473 normalized473 rows473 checked473
  · exact extensions_of_normalized 474 free474 normalized474 rows474 checked474
  · exact extensions_of_normalized 475 free475 normalized475 rows475 checked475
  · exact extensions_of_normalized 476 free476 normalized476 rows476 checked476
  · exact extensions_of_normalized 477 free477 normalized477 rows477 checked477
  · exact extensions_of_normalized 478 free478 normalized478 rows478 checked478
  · exact extensions_of_normalized 479 free479 normalized479 rows479 checked479

end QiushiMatmul.GlobalOrbit.Cases29
