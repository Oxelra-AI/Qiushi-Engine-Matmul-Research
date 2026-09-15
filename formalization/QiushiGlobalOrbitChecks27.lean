import QiushiGlobalOrbitData27

namespace QiushiMatmul.GlobalOrbit.Cases27
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem normalized432 : NormalizationCheck (frozenWangBasis 432) free432 := by
  decide +kernel +revert

theorem checked432 : ∀ k : Fin (2 ^ free432.length), TransitionCheck 432 (unpackCode free432 k.val) (rows432 k) := by
  decide +kernel +revert

theorem normalized433 : NormalizationCheck (frozenWangBasis 433) free433 := by
  decide +kernel +revert

theorem checked433 : ∀ k : Fin (2 ^ free433.length), TransitionCheck 433 (unpackCode free433 k.val) (rows433 k) := by
  decide +kernel +revert

theorem normalized434 : NormalizationCheck (frozenWangBasis 434) free434 := by
  decide +kernel +revert

theorem checked434 : ∀ k : Fin (2 ^ free434.length), TransitionCheck 434 (unpackCode free434 k.val) (rows434 k) := by
  decide +kernel +revert

theorem normalized435 : NormalizationCheck (frozenWangBasis 435) free435 := by
  decide +kernel +revert

theorem checked435 : ∀ k : Fin (2 ^ free435.length), TransitionCheck 435 (unpackCode free435 k.val) (rows435 k) := by
  decide +kernel +revert

theorem normalized436 : NormalizationCheck (frozenWangBasis 436) free436 := by
  decide +kernel +revert

theorem checked436 : ∀ k : Fin (2 ^ free436.length), TransitionCheck 436 (unpackCode free436 k.val) (rows436 k) := by
  decide +kernel +revert

theorem normalized437 : NormalizationCheck (frozenWangBasis 437) free437 := by
  decide +kernel +revert

theorem checked437 : ∀ k : Fin (2 ^ free437.length), TransitionCheck 437 (unpackCode free437 k.val) (rows437 k) := by
  decide +kernel +revert

theorem normalized438 : NormalizationCheck (frozenWangBasis 438) free438 := by
  decide +kernel +revert

theorem checked438 : ∀ k : Fin (2 ^ free438.length), TransitionCheck 438 (unpackCode free438 k.val) (rows438 k) := by
  decide +kernel +revert

theorem normalized439 : NormalizationCheck (frozenWangBasis 439) free439 := by
  decide +kernel +revert

theorem checked439 : ∀ k : Fin (2 ^ free439.length), TransitionCheck 439 (unpackCode free439 k.val) (rows439 k) := by
  decide +kernel +revert

theorem normalized440 : NormalizationCheck (frozenWangBasis 440) free440 := by
  decide +kernel +revert

theorem checked440 : ∀ k : Fin (2 ^ free440.length), TransitionCheck 440 (unpackCode free440 k.val) (rows440 k) := by
  decide +kernel +revert

theorem normalized441 : NormalizationCheck (frozenWangBasis 441) free441 := by
  decide +kernel +revert

theorem checked441 : ∀ k : Fin (2 ^ free441.length), TransitionCheck 441 (unpackCode free441 k.val) (rows441 k) := by
  decide +kernel +revert

theorem normalized442 : NormalizationCheck (frozenWangBasis 442) free442 := by
  decide +kernel +revert

theorem checked442 : ∀ k : Fin (2 ^ free442.length), TransitionCheck 442 (unpackCode free442 k.val) (rows442 k) := by
  decide +kernel +revert

theorem normalized443 : NormalizationCheck (frozenWangBasis 443) free443 := by
  decide +kernel +revert

theorem checked443 : ∀ k : Fin (2 ^ free443.length), TransitionCheck 443 (unpackCode free443 k.val) (rows443 k) := by
  decide +kernel +revert

theorem normalized444 : NormalizationCheck (frozenWangBasis 444) free444 := by
  decide +kernel +revert

theorem checked444 : ∀ k : Fin (2 ^ free444.length), TransitionCheck 444 (unpackCode free444 k.val) (rows444 k) := by
  decide +kernel +revert

theorem normalized445 : NormalizationCheck (frozenWangBasis 445) free445 := by
  decide +kernel +revert

theorem checked445 : ∀ k : Fin (2 ^ free445.length), TransitionCheck 445 (unpackCode free445 k.val) (rows445 k) := by
  decide +kernel +revert

theorem normalized446 : NormalizationCheck (frozenWangBasis 446) free446 := by
  decide +kernel +revert

theorem checked446 : ∀ k : Fin (2 ^ free446.length), TransitionCheck 446 (unpackCode free446 k.val) (rows446 k) := by
  decide +kernel +revert

theorem normalized447 : NormalizationCheck (frozenWangBasis 447) free447 := by
  decide +kernel +revert

theorem checked447 : ∀ k : Fin (2 ^ free447.length), TransitionCheck 447 (unpackCode free447 k.val) (rows447 k) := by
  decide +kernel +revert

theorem covered (j : Fin 16) : ∀ c : Fin 512,
    Covered (spanCodes (c.val :: frozenWangBasis ⟨432 + j.val, by omega⟩)) := by
  fin_cases j
  · exact extensions_of_normalized 432 free432 normalized432 rows432 checked432
  · exact extensions_of_normalized 433 free433 normalized433 rows433 checked433
  · exact extensions_of_normalized 434 free434 normalized434 rows434 checked434
  · exact extensions_of_normalized 435 free435 normalized435 rows435 checked435
  · exact extensions_of_normalized 436 free436 normalized436 rows436 checked436
  · exact extensions_of_normalized 437 free437 normalized437 rows437 checked437
  · exact extensions_of_normalized 438 free438 normalized438 rows438 checked438
  · exact extensions_of_normalized 439 free439 normalized439 rows439 checked439
  · exact extensions_of_normalized 440 free440 normalized440 rows440 checked440
  · exact extensions_of_normalized 441 free441 normalized441 rows441 checked441
  · exact extensions_of_normalized 442 free442 normalized442 rows442 checked442
  · exact extensions_of_normalized 443 free443 normalized443 rows443 checked443
  · exact extensions_of_normalized 444 free444 normalized444 rows444 checked444
  · exact extensions_of_normalized 445 free445 normalized445 rows445 checked445
  · exact extensions_of_normalized 446 free446 normalized446 rows446 checked446
  · exact extensions_of_normalized 447 free447 normalized447 rows447 checked447

end QiushiMatmul.GlobalOrbit.Cases27
