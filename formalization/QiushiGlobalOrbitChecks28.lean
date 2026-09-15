import QiushiGlobalOrbitData28

namespace QiushiMatmul.GlobalOrbit.Cases28
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem normalized448 : NormalizationCheck (frozenWangBasis 448) free448 := by
  decide +kernel +revert

theorem checked448 : ∀ k : Fin (2 ^ free448.length), TransitionCheck 448 (unpackCode free448 k.val) (rows448 k) := by
  decide +kernel +revert

theorem normalized449 : NormalizationCheck (frozenWangBasis 449) free449 := by
  decide +kernel +revert

theorem checked449 : ∀ k : Fin (2 ^ free449.length), TransitionCheck 449 (unpackCode free449 k.val) (rows449 k) := by
  decide +kernel +revert

theorem normalized450 : NormalizationCheck (frozenWangBasis 450) free450 := by
  decide +kernel +revert

theorem checked450 : ∀ k : Fin (2 ^ free450.length), TransitionCheck 450 (unpackCode free450 k.val) (rows450 k) := by
  decide +kernel +revert

theorem normalized451 : NormalizationCheck (frozenWangBasis 451) free451 := by
  decide +kernel +revert

theorem checked451 : ∀ k : Fin (2 ^ free451.length), TransitionCheck 451 (unpackCode free451 k.val) (rows451 k) := by
  decide +kernel +revert

theorem normalized452 : NormalizationCheck (frozenWangBasis 452) free452 := by
  decide +kernel +revert

theorem checked452 : ∀ k : Fin (2 ^ free452.length), TransitionCheck 452 (unpackCode free452 k.val) (rows452 k) := by
  decide +kernel +revert

theorem normalized453 : NormalizationCheck (frozenWangBasis 453) free453 := by
  decide +kernel +revert

theorem checked453 : ∀ k : Fin (2 ^ free453.length), TransitionCheck 453 (unpackCode free453 k.val) (rows453 k) := by
  decide +kernel +revert

theorem normalized454 : NormalizationCheck (frozenWangBasis 454) free454 := by
  decide +kernel +revert

theorem checked454 : ∀ k : Fin (2 ^ free454.length), TransitionCheck 454 (unpackCode free454 k.val) (rows454 k) := by
  decide +kernel +revert

theorem normalized455 : NormalizationCheck (frozenWangBasis 455) free455 := by
  decide +kernel +revert

theorem checked455 : ∀ k : Fin (2 ^ free455.length), TransitionCheck 455 (unpackCode free455 k.val) (rows455 k) := by
  decide +kernel +revert

theorem normalized456 : NormalizationCheck (frozenWangBasis 456) free456 := by
  decide +kernel +revert

theorem checked456 : ∀ k : Fin (2 ^ free456.length), TransitionCheck 456 (unpackCode free456 k.val) (rows456 k) := by
  decide +kernel +revert

theorem normalized457 : NormalizationCheck (frozenWangBasis 457) free457 := by
  decide +kernel +revert

theorem checked457 : ∀ k : Fin (2 ^ free457.length), TransitionCheck 457 (unpackCode free457 k.val) (rows457 k) := by
  decide +kernel +revert

theorem normalized458 : NormalizationCheck (frozenWangBasis 458) free458 := by
  decide +kernel +revert

theorem checked458 : ∀ k : Fin (2 ^ free458.length), TransitionCheck 458 (unpackCode free458 k.val) (rows458 k) := by
  decide +kernel +revert

theorem normalized459 : NormalizationCheck (frozenWangBasis 459) free459 := by
  decide +kernel +revert

theorem checked459 : ∀ k : Fin (2 ^ free459.length), TransitionCheck 459 (unpackCode free459 k.val) (rows459 k) := by
  decide +kernel +revert

theorem normalized460 : NormalizationCheck (frozenWangBasis 460) free460 := by
  decide +kernel +revert

theorem checked460 : ∀ k : Fin (2 ^ free460.length), TransitionCheck 460 (unpackCode free460 k.val) (rows460 k) := by
  decide +kernel +revert

theorem normalized461 : NormalizationCheck (frozenWangBasis 461) free461 := by
  decide +kernel +revert

theorem checked461 : ∀ k : Fin (2 ^ free461.length), TransitionCheck 461 (unpackCode free461 k.val) (rows461 k) := by
  decide +kernel +revert

theorem normalized462 : NormalizationCheck (frozenWangBasis 462) free462 := by
  decide +kernel +revert

theorem checked462 : ∀ k : Fin (2 ^ free462.length), TransitionCheck 462 (unpackCode free462 k.val) (rows462 k) := by
  decide +kernel +revert

theorem normalized463 : NormalizationCheck (frozenWangBasis 463) free463 := by
  decide +kernel +revert

theorem checked463 : ∀ k : Fin (2 ^ free463.length), TransitionCheck 463 (unpackCode free463 k.val) (rows463 k) := by
  decide +kernel +revert

theorem covered (j : Fin 16) : ∀ c : Fin 512,
    Covered (spanCodes (c.val :: frozenWangBasis ⟨448 + j.val, by omega⟩)) := by
  fin_cases j
  · exact extensions_of_normalized 448 free448 normalized448 rows448 checked448
  · exact extensions_of_normalized 449 free449 normalized449 rows449 checked449
  · exact extensions_of_normalized 450 free450 normalized450 rows450 checked450
  · exact extensions_of_normalized 451 free451 normalized451 rows451 checked451
  · exact extensions_of_normalized 452 free452 normalized452 rows452 checked452
  · exact extensions_of_normalized 453 free453 normalized453 rows453 checked453
  · exact extensions_of_normalized 454 free454 normalized454 rows454 checked454
  · exact extensions_of_normalized 455 free455 normalized455 rows455 checked455
  · exact extensions_of_normalized 456 free456 normalized456 rows456 checked456
  · exact extensions_of_normalized 457 free457 normalized457 rows457 checked457
  · exact extensions_of_normalized 458 free458 normalized458 rows458 checked458
  · exact extensions_of_normalized 459 free459 normalized459 rows459 checked459
  · exact extensions_of_normalized 460 free460 normalized460 rows460 checked460
  · exact extensions_of_normalized 461 free461 normalized461 rows461 checked461
  · exact extensions_of_normalized 462 free462 normalized462 rows462 checked462
  · exact extensions_of_normalized 463 free463 normalized463 rows463 checked463

end QiushiMatmul.GlobalOrbit.Cases28
