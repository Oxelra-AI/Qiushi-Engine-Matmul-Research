import QiushiGlobalOrbitData19

namespace QiushiMatmul.GlobalOrbit.Cases19
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem normalized304 : NormalizationCheck (frozenWangBasis 304) free304 := by
  decide +kernel +revert

theorem checked304 : ∀ k : Fin (2 ^ free304.length), TransitionCheck 304 (unpackCode free304 k.val) (rows304 k) := by
  decide +kernel +revert

theorem normalized305 : NormalizationCheck (frozenWangBasis 305) free305 := by
  decide +kernel +revert

theorem checked305 : ∀ k : Fin (2 ^ free305.length), TransitionCheck 305 (unpackCode free305 k.val) (rows305 k) := by
  decide +kernel +revert

theorem normalized306 : NormalizationCheck (frozenWangBasis 306) free306 := by
  decide +kernel +revert

theorem checked306 : ∀ k : Fin (2 ^ free306.length), TransitionCheck 306 (unpackCode free306 k.val) (rows306 k) := by
  decide +kernel +revert

theorem normalized307 : NormalizationCheck (frozenWangBasis 307) free307 := by
  decide +kernel +revert

theorem checked307 : ∀ k : Fin (2 ^ free307.length), TransitionCheck 307 (unpackCode free307 k.val) (rows307 k) := by
  decide +kernel +revert

theorem normalized308 : NormalizationCheck (frozenWangBasis 308) free308 := by
  decide +kernel +revert

theorem checked308 : ∀ k : Fin (2 ^ free308.length), TransitionCheck 308 (unpackCode free308 k.val) (rows308 k) := by
  decide +kernel +revert

theorem normalized309 : NormalizationCheck (frozenWangBasis 309) free309 := by
  decide +kernel +revert

theorem checked309 : ∀ k : Fin (2 ^ free309.length), TransitionCheck 309 (unpackCode free309 k.val) (rows309 k) := by
  decide +kernel +revert

theorem normalized310 : NormalizationCheck (frozenWangBasis 310) free310 := by
  decide +kernel +revert

theorem checked310 : ∀ k : Fin (2 ^ free310.length), TransitionCheck 310 (unpackCode free310 k.val) (rows310 k) := by
  decide +kernel +revert

theorem normalized311 : NormalizationCheck (frozenWangBasis 311) free311 := by
  decide +kernel +revert

theorem checked311 : ∀ k : Fin (2 ^ free311.length), TransitionCheck 311 (unpackCode free311 k.val) (rows311 k) := by
  decide +kernel +revert

theorem normalized312 : NormalizationCheck (frozenWangBasis 312) free312 := by
  decide +kernel +revert

theorem checked312 : ∀ k : Fin (2 ^ free312.length), TransitionCheck 312 (unpackCode free312 k.val) (rows312 k) := by
  decide +kernel +revert

theorem normalized313 : NormalizationCheck (frozenWangBasis 313) free313 := by
  decide +kernel +revert

theorem checked313 : ∀ k : Fin (2 ^ free313.length), TransitionCheck 313 (unpackCode free313 k.val) (rows313 k) := by
  decide +kernel +revert

theorem normalized314 : NormalizationCheck (frozenWangBasis 314) free314 := by
  decide +kernel +revert

theorem checked314 : ∀ k : Fin (2 ^ free314.length), TransitionCheck 314 (unpackCode free314 k.val) (rows314 k) := by
  decide +kernel +revert

theorem normalized315 : NormalizationCheck (frozenWangBasis 315) free315 := by
  decide +kernel +revert

theorem checked315 : ∀ k : Fin (2 ^ free315.length), TransitionCheck 315 (unpackCode free315 k.val) (rows315 k) := by
  decide +kernel +revert

theorem normalized316 : NormalizationCheck (frozenWangBasis 316) free316 := by
  decide +kernel +revert

theorem checked316 : ∀ k : Fin (2 ^ free316.length), TransitionCheck 316 (unpackCode free316 k.val) (rows316 k) := by
  decide +kernel +revert

theorem normalized317 : NormalizationCheck (frozenWangBasis 317) free317 := by
  decide +kernel +revert

theorem checked317 : ∀ k : Fin (2 ^ free317.length), TransitionCheck 317 (unpackCode free317 k.val) (rows317 k) := by
  decide +kernel +revert

theorem normalized318 : NormalizationCheck (frozenWangBasis 318) free318 := by
  decide +kernel +revert

theorem checked318 : ∀ k : Fin (2 ^ free318.length), TransitionCheck 318 (unpackCode free318 k.val) (rows318 k) := by
  decide +kernel +revert

theorem normalized319 : NormalizationCheck (frozenWangBasis 319) free319 := by
  decide +kernel +revert

theorem checked319 : ∀ k : Fin (2 ^ free319.length), TransitionCheck 319 (unpackCode free319 k.val) (rows319 k) := by
  decide +kernel +revert

theorem covered (j : Fin 16) : ∀ c : Fin 512,
    Covered (spanCodes (c.val :: frozenWangBasis ⟨304 + j.val, by omega⟩)) := by
  fin_cases j
  · exact extensions_of_normalized 304 free304 normalized304 rows304 checked304
  · exact extensions_of_normalized 305 free305 normalized305 rows305 checked305
  · exact extensions_of_normalized 306 free306 normalized306 rows306 checked306
  · exact extensions_of_normalized 307 free307 normalized307 rows307 checked307
  · exact extensions_of_normalized 308 free308 normalized308 rows308 checked308
  · exact extensions_of_normalized 309 free309 normalized309 rows309 checked309
  · exact extensions_of_normalized 310 free310 normalized310 rows310 checked310
  · exact extensions_of_normalized 311 free311 normalized311 rows311 checked311
  · exact extensions_of_normalized 312 free312 normalized312 rows312 checked312
  · exact extensions_of_normalized 313 free313 normalized313 rows313 checked313
  · exact extensions_of_normalized 314 free314 normalized314 rows314 checked314
  · exact extensions_of_normalized 315 free315 normalized315 rows315 checked315
  · exact extensions_of_normalized 316 free316 normalized316 rows316 checked316
  · exact extensions_of_normalized 317 free317 normalized317 rows317 checked317
  · exact extensions_of_normalized 318 free318 normalized318 rows318 checked318
  · exact extensions_of_normalized 319 free319 normalized319 rows319 checked319

end QiushiMatmul.GlobalOrbit.Cases19
