import QiushiGlobalOrbitData30

namespace QiushiMatmul.GlobalOrbit.Cases30
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem normalized480 : NormalizationCheck (frozenWangBasis 480) free480 := by
  decide +kernel +revert

theorem checked480 : ∀ k : Fin (2 ^ free480.length), TransitionCheck 480 (unpackCode free480 k.val) (rows480 k) := by
  decide +kernel +revert

theorem normalized481 : NormalizationCheck (frozenWangBasis 481) free481 := by
  decide +kernel +revert

theorem checked481 : ∀ k : Fin (2 ^ free481.length), TransitionCheck 481 (unpackCode free481 k.val) (rows481 k) := by
  decide +kernel +revert

theorem normalized482 : NormalizationCheck (frozenWangBasis 482) free482 := by
  decide +kernel +revert

theorem checked482 : ∀ k : Fin (2 ^ free482.length), TransitionCheck 482 (unpackCode free482 k.val) (rows482 k) := by
  decide +kernel +revert

theorem normalized483 : NormalizationCheck (frozenWangBasis 483) free483 := by
  decide +kernel +revert

theorem checked483 : ∀ k : Fin (2 ^ free483.length), TransitionCheck 483 (unpackCode free483 k.val) (rows483 k) := by
  decide +kernel +revert

theorem normalized484 : NormalizationCheck (frozenWangBasis 484) free484 := by
  decide +kernel +revert

theorem checked484 : ∀ k : Fin (2 ^ free484.length), TransitionCheck 484 (unpackCode free484 k.val) (rows484 k) := by
  decide +kernel +revert

theorem normalized485 : NormalizationCheck (frozenWangBasis 485) free485 := by
  decide +kernel +revert

theorem checked485 : ∀ k : Fin (2 ^ free485.length), TransitionCheck 485 (unpackCode free485 k.val) (rows485 k) := by
  decide +kernel +revert

theorem normalized486 : NormalizationCheck (frozenWangBasis 486) free486 := by
  decide +kernel +revert

theorem checked486 : ∀ k : Fin (2 ^ free486.length), TransitionCheck 486 (unpackCode free486 k.val) (rows486 k) := by
  decide +kernel +revert

theorem normalized487 : NormalizationCheck (frozenWangBasis 487) free487 := by
  decide +kernel +revert

theorem checked487 : ∀ k : Fin (2 ^ free487.length), TransitionCheck 487 (unpackCode free487 k.val) (rows487 k) := by
  decide +kernel +revert

theorem normalized488 : NormalizationCheck (frozenWangBasis 488) free488 := by
  decide +kernel +revert

theorem checked488 : ∀ k : Fin (2 ^ free488.length), TransitionCheck 488 (unpackCode free488 k.val) (rows488 k) := by
  decide +kernel +revert

theorem normalized489 : NormalizationCheck (frozenWangBasis 489) free489 := by
  decide +kernel +revert

theorem checked489 : ∀ k : Fin (2 ^ free489.length), TransitionCheck 489 (unpackCode free489 k.val) (rows489 k) := by
  decide +kernel +revert

theorem normalized490 : NormalizationCheck (frozenWangBasis 490) free490 := by
  decide +kernel +revert

theorem checked490 : ∀ k : Fin (2 ^ free490.length), TransitionCheck 490 (unpackCode free490 k.val) (rows490 k) := by
  decide +kernel +revert

theorem normalized491 : NormalizationCheck (frozenWangBasis 491) free491 := by
  decide +kernel +revert

theorem checked491 : ∀ k : Fin (2 ^ free491.length), TransitionCheck 491 (unpackCode free491 k.val) (rows491 k) := by
  decide +kernel +revert

theorem normalized492 : NormalizationCheck (frozenWangBasis 492) free492 := by
  decide +kernel +revert

theorem checked492 : ∀ k : Fin (2 ^ free492.length), TransitionCheck 492 (unpackCode free492 k.val) (rows492 k) := by
  decide +kernel +revert

theorem normalized493 : NormalizationCheck (frozenWangBasis 493) free493 := by
  decide +kernel +revert

theorem checked493 : ∀ k : Fin (2 ^ free493.length), TransitionCheck 493 (unpackCode free493 k.val) (rows493 k) := by
  decide +kernel +revert

theorem normalized494 : NormalizationCheck (frozenWangBasis 494) free494 := by
  decide +kernel +revert

theorem checked494 : ∀ k : Fin (2 ^ free494.length), TransitionCheck 494 (unpackCode free494 k.val) (rows494 k) := by
  decide +kernel +revert

theorem normalized495 : NormalizationCheck (frozenWangBasis 495) free495 := by
  decide +kernel +revert

theorem checked495 : ∀ k : Fin (2 ^ free495.length), TransitionCheck 495 (unpackCode free495 k.val) (rows495 k) := by
  decide +kernel +revert

theorem covered (j : Fin 16) : ∀ c : Fin 512,
    Covered (spanCodes (c.val :: frozenWangBasis ⟨480 + j.val, by omega⟩)) := by
  fin_cases j
  · exact extensions_of_normalized 480 free480 normalized480 rows480 checked480
  · exact extensions_of_normalized 481 free481 normalized481 rows481 checked481
  · exact extensions_of_normalized 482 free482 normalized482 rows482 checked482
  · exact extensions_of_normalized 483 free483 normalized483 rows483 checked483
  · exact extensions_of_normalized 484 free484 normalized484 rows484 checked484
  · exact extensions_of_normalized 485 free485 normalized485 rows485 checked485
  · exact extensions_of_normalized 486 free486 normalized486 rows486 checked486
  · exact extensions_of_normalized 487 free487 normalized487 rows487 checked487
  · exact extensions_of_normalized 488 free488 normalized488 rows488 checked488
  · exact extensions_of_normalized 489 free489 normalized489 rows489 checked489
  · exact extensions_of_normalized 490 free490 normalized490 rows490 checked490
  · exact extensions_of_normalized 491 free491 normalized491 rows491 checked491
  · exact extensions_of_normalized 492 free492 normalized492 rows492 checked492
  · exact extensions_of_normalized 493 free493 normalized493 rows493 checked493
  · exact extensions_of_normalized 494 free494 normalized494 rows494 checked494
  · exact extensions_of_normalized 495 free495 normalized495 rows495 checked495

end QiushiMatmul.GlobalOrbit.Cases30
