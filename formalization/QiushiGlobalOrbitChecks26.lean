import QiushiGlobalOrbitData26

namespace QiushiMatmul.GlobalOrbit.Cases26
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem normalized416 : NormalizationCheck (frozenWangBasis 416) free416 := by
  decide +kernel +revert

theorem checked416 : ∀ k : Fin (2 ^ free416.length), TransitionCheck 416 (unpackCode free416 k.val) (rows416 k) := by
  decide +kernel +revert

theorem normalized417 : NormalizationCheck (frozenWangBasis 417) free417 := by
  decide +kernel +revert

theorem checked417 : ∀ k : Fin (2 ^ free417.length), TransitionCheck 417 (unpackCode free417 k.val) (rows417 k) := by
  decide +kernel +revert

theorem normalized418 : NormalizationCheck (frozenWangBasis 418) free418 := by
  decide +kernel +revert

theorem checked418 : ∀ k : Fin (2 ^ free418.length), TransitionCheck 418 (unpackCode free418 k.val) (rows418 k) := by
  decide +kernel +revert

theorem normalized419 : NormalizationCheck (frozenWangBasis 419) free419 := by
  decide +kernel +revert

theorem checked419 : ∀ k : Fin (2 ^ free419.length), TransitionCheck 419 (unpackCode free419 k.val) (rows419 k) := by
  decide +kernel +revert

theorem normalized420 : NormalizationCheck (frozenWangBasis 420) free420 := by
  decide +kernel +revert

theorem checked420 : ∀ k : Fin (2 ^ free420.length), TransitionCheck 420 (unpackCode free420 k.val) (rows420 k) := by
  decide +kernel +revert

theorem normalized421 : NormalizationCheck (frozenWangBasis 421) free421 := by
  decide +kernel +revert

theorem checked421 : ∀ k : Fin (2 ^ free421.length), TransitionCheck 421 (unpackCode free421 k.val) (rows421 k) := by
  decide +kernel +revert

theorem normalized422 : NormalizationCheck (frozenWangBasis 422) free422 := by
  decide +kernel +revert

theorem checked422 : ∀ k : Fin (2 ^ free422.length), TransitionCheck 422 (unpackCode free422 k.val) (rows422 k) := by
  decide +kernel +revert

theorem normalized423 : NormalizationCheck (frozenWangBasis 423) free423 := by
  decide +kernel +revert

theorem checked423 : ∀ k : Fin (2 ^ free423.length), TransitionCheck 423 (unpackCode free423 k.val) (rows423 k) := by
  decide +kernel +revert

theorem normalized424 : NormalizationCheck (frozenWangBasis 424) free424 := by
  decide +kernel +revert

theorem checked424 : ∀ k : Fin (2 ^ free424.length), TransitionCheck 424 (unpackCode free424 k.val) (rows424 k) := by
  decide +kernel +revert

theorem normalized425 : NormalizationCheck (frozenWangBasis 425) free425 := by
  decide +kernel +revert

theorem checked425 : ∀ k : Fin (2 ^ free425.length), TransitionCheck 425 (unpackCode free425 k.val) (rows425 k) := by
  decide +kernel +revert

theorem normalized426 : NormalizationCheck (frozenWangBasis 426) free426 := by
  decide +kernel +revert

theorem checked426 : ∀ k : Fin (2 ^ free426.length), TransitionCheck 426 (unpackCode free426 k.val) (rows426 k) := by
  decide +kernel +revert

theorem normalized427 : NormalizationCheck (frozenWangBasis 427) free427 := by
  decide +kernel +revert

theorem checked427 : ∀ k : Fin (2 ^ free427.length), TransitionCheck 427 (unpackCode free427 k.val) (rows427 k) := by
  decide +kernel +revert

theorem normalized428 : NormalizationCheck (frozenWangBasis 428) free428 := by
  decide +kernel +revert

theorem checked428 : ∀ k : Fin (2 ^ free428.length), TransitionCheck 428 (unpackCode free428 k.val) (rows428 k) := by
  decide +kernel +revert

theorem normalized429 : NormalizationCheck (frozenWangBasis 429) free429 := by
  decide +kernel +revert

theorem checked429 : ∀ k : Fin (2 ^ free429.length), TransitionCheck 429 (unpackCode free429 k.val) (rows429 k) := by
  decide +kernel +revert

theorem normalized430 : NormalizationCheck (frozenWangBasis 430) free430 := by
  decide +kernel +revert

theorem checked430 : ∀ k : Fin (2 ^ free430.length), TransitionCheck 430 (unpackCode free430 k.val) (rows430 k) := by
  decide +kernel +revert

theorem normalized431 : NormalizationCheck (frozenWangBasis 431) free431 := by
  decide +kernel +revert

theorem checked431 : ∀ k : Fin (2 ^ free431.length), TransitionCheck 431 (unpackCode free431 k.val) (rows431 k) := by
  decide +kernel +revert

theorem covered (j : Fin 16) : ∀ c : Fin 512,
    Covered (spanCodes (c.val :: frozenWangBasis ⟨416 + j.val, by omega⟩)) := by
  fin_cases j
  · exact extensions_of_normalized 416 free416 normalized416 rows416 checked416
  · exact extensions_of_normalized 417 free417 normalized417 rows417 checked417
  · exact extensions_of_normalized 418 free418 normalized418 rows418 checked418
  · exact extensions_of_normalized 419 free419 normalized419 rows419 checked419
  · exact extensions_of_normalized 420 free420 normalized420 rows420 checked420
  · exact extensions_of_normalized 421 free421 normalized421 rows421 checked421
  · exact extensions_of_normalized 422 free422 normalized422 rows422 checked422
  · exact extensions_of_normalized 423 free423 normalized423 rows423 checked423
  · exact extensions_of_normalized 424 free424 normalized424 rows424 checked424
  · exact extensions_of_normalized 425 free425 normalized425 rows425 checked425
  · exact extensions_of_normalized 426 free426 normalized426 rows426 checked426
  · exact extensions_of_normalized 427 free427 normalized427 rows427 checked427
  · exact extensions_of_normalized 428 free428 normalized428 rows428 checked428
  · exact extensions_of_normalized 429 free429 normalized429 rows429 checked429
  · exact extensions_of_normalized 430 free430 normalized430 rows430 checked430
  · exact extensions_of_normalized 431 free431 normalized431 rows431 checked431

end QiushiMatmul.GlobalOrbit.Cases26
