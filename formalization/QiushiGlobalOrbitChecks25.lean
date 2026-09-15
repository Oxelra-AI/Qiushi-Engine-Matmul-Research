import QiushiGlobalOrbitData25

namespace QiushiMatmul.GlobalOrbit.Cases25
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem normalized400 : NormalizationCheck (frozenWangBasis 400) free400 := by
  decide +kernel +revert

theorem checked400 : ∀ k : Fin (2 ^ free400.length), TransitionCheck 400 (unpackCode free400 k.val) (rows400 k) := by
  decide +kernel +revert

theorem normalized401 : NormalizationCheck (frozenWangBasis 401) free401 := by
  decide +kernel +revert

theorem checked401 : ∀ k : Fin (2 ^ free401.length), TransitionCheck 401 (unpackCode free401 k.val) (rows401 k) := by
  decide +kernel +revert

theorem normalized402 : NormalizationCheck (frozenWangBasis 402) free402 := by
  decide +kernel +revert

theorem checked402 : ∀ k : Fin (2 ^ free402.length), TransitionCheck 402 (unpackCode free402 k.val) (rows402 k) := by
  decide +kernel +revert

theorem normalized403 : NormalizationCheck (frozenWangBasis 403) free403 := by
  decide +kernel +revert

theorem checked403 : ∀ k : Fin (2 ^ free403.length), TransitionCheck 403 (unpackCode free403 k.val) (rows403 k) := by
  decide +kernel +revert

theorem normalized404 : NormalizationCheck (frozenWangBasis 404) free404 := by
  decide +kernel +revert

theorem checked404 : ∀ k : Fin (2 ^ free404.length), TransitionCheck 404 (unpackCode free404 k.val) (rows404 k) := by
  decide +kernel +revert

theorem normalized405 : NormalizationCheck (frozenWangBasis 405) free405 := by
  decide +kernel +revert

theorem checked405 : ∀ k : Fin (2 ^ free405.length), TransitionCheck 405 (unpackCode free405 k.val) (rows405 k) := by
  decide +kernel +revert

theorem normalized406 : NormalizationCheck (frozenWangBasis 406) free406 := by
  decide +kernel +revert

theorem checked406 : ∀ k : Fin (2 ^ free406.length), TransitionCheck 406 (unpackCode free406 k.val) (rows406 k) := by
  decide +kernel +revert

theorem normalized407 : NormalizationCheck (frozenWangBasis 407) free407 := by
  decide +kernel +revert

theorem checked407 : ∀ k : Fin (2 ^ free407.length), TransitionCheck 407 (unpackCode free407 k.val) (rows407 k) := by
  decide +kernel +revert

theorem normalized408 : NormalizationCheck (frozenWangBasis 408) free408 := by
  decide +kernel +revert

theorem checked408 : ∀ k : Fin (2 ^ free408.length), TransitionCheck 408 (unpackCode free408 k.val) (rows408 k) := by
  decide +kernel +revert

theorem normalized409 : NormalizationCheck (frozenWangBasis 409) free409 := by
  decide +kernel +revert

theorem checked409 : ∀ k : Fin (2 ^ free409.length), TransitionCheck 409 (unpackCode free409 k.val) (rows409 k) := by
  decide +kernel +revert

theorem normalized410 : NormalizationCheck (frozenWangBasis 410) free410 := by
  decide +kernel +revert

theorem checked410 : ∀ k : Fin (2 ^ free410.length), TransitionCheck 410 (unpackCode free410 k.val) (rows410 k) := by
  decide +kernel +revert

theorem normalized411 : NormalizationCheck (frozenWangBasis 411) free411 := by
  decide +kernel +revert

theorem checked411 : ∀ k : Fin (2 ^ free411.length), TransitionCheck 411 (unpackCode free411 k.val) (rows411 k) := by
  decide +kernel +revert

theorem normalized412 : NormalizationCheck (frozenWangBasis 412) free412 := by
  decide +kernel +revert

theorem checked412 : ∀ k : Fin (2 ^ free412.length), TransitionCheck 412 (unpackCode free412 k.val) (rows412 k) := by
  decide +kernel +revert

theorem normalized413 : NormalizationCheck (frozenWangBasis 413) free413 := by
  decide +kernel +revert

theorem checked413 : ∀ k : Fin (2 ^ free413.length), TransitionCheck 413 (unpackCode free413 k.val) (rows413 k) := by
  decide +kernel +revert

theorem normalized414 : NormalizationCheck (frozenWangBasis 414) free414 := by
  decide +kernel +revert

theorem checked414 : ∀ k : Fin (2 ^ free414.length), TransitionCheck 414 (unpackCode free414 k.val) (rows414 k) := by
  decide +kernel +revert

theorem normalized415 : NormalizationCheck (frozenWangBasis 415) free415 := by
  decide +kernel +revert

theorem checked415 : ∀ k : Fin (2 ^ free415.length), TransitionCheck 415 (unpackCode free415 k.val) (rows415 k) := by
  decide +kernel +revert

theorem covered (j : Fin 16) : ∀ c : Fin 512,
    Covered (spanCodes (c.val :: frozenWangBasis ⟨400 + j.val, by omega⟩)) := by
  fin_cases j
  · exact extensions_of_normalized 400 free400 normalized400 rows400 checked400
  · exact extensions_of_normalized 401 free401 normalized401 rows401 checked401
  · exact extensions_of_normalized 402 free402 normalized402 rows402 checked402
  · exact extensions_of_normalized 403 free403 normalized403 rows403 checked403
  · exact extensions_of_normalized 404 free404 normalized404 rows404 checked404
  · exact extensions_of_normalized 405 free405 normalized405 rows405 checked405
  · exact extensions_of_normalized 406 free406 normalized406 rows406 checked406
  · exact extensions_of_normalized 407 free407 normalized407 rows407 checked407
  · exact extensions_of_normalized 408 free408 normalized408 rows408 checked408
  · exact extensions_of_normalized 409 free409 normalized409 rows409 checked409
  · exact extensions_of_normalized 410 free410 normalized410 rows410 checked410
  · exact extensions_of_normalized 411 free411 normalized411 rows411 checked411
  · exact extensions_of_normalized 412 free412 normalized412 rows412 checked412
  · exact extensions_of_normalized 413 free413 normalized413 rows413 checked413
  · exact extensions_of_normalized 414 free414 normalized414 rows414 checked414
  · exact extensions_of_normalized 415 free415 normalized415 rows415 checked415

end QiushiMatmul.GlobalOrbit.Cases25
