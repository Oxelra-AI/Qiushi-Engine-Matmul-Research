import QiushiGlobalOrbitData20

namespace QiushiMatmul.GlobalOrbit.Cases20
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem normalized320 : NormalizationCheck (frozenWangBasis 320) free320 := by
  decide +kernel +revert

theorem checked320 : ∀ k : Fin (2 ^ free320.length), TransitionCheck 320 (unpackCode free320 k.val) (rows320 k) := by
  decide +kernel +revert

theorem normalized321 : NormalizationCheck (frozenWangBasis 321) free321 := by
  decide +kernel +revert

theorem checked321 : ∀ k : Fin (2 ^ free321.length), TransitionCheck 321 (unpackCode free321 k.val) (rows321 k) := by
  decide +kernel +revert

theorem normalized322 : NormalizationCheck (frozenWangBasis 322) free322 := by
  decide +kernel +revert

theorem checked322 : ∀ k : Fin (2 ^ free322.length), TransitionCheck 322 (unpackCode free322 k.val) (rows322 k) := by
  decide +kernel +revert

theorem normalized323 : NormalizationCheck (frozenWangBasis 323) free323 := by
  decide +kernel +revert

theorem checked323 : ∀ k : Fin (2 ^ free323.length), TransitionCheck 323 (unpackCode free323 k.val) (rows323 k) := by
  decide +kernel +revert

theorem normalized324 : NormalizationCheck (frozenWangBasis 324) free324 := by
  decide +kernel +revert

theorem checked324 : ∀ k : Fin (2 ^ free324.length), TransitionCheck 324 (unpackCode free324 k.val) (rows324 k) := by
  decide +kernel +revert

theorem normalized325 : NormalizationCheck (frozenWangBasis 325) free325 := by
  decide +kernel +revert

theorem checked325 : ∀ k : Fin (2 ^ free325.length), TransitionCheck 325 (unpackCode free325 k.val) (rows325 k) := by
  decide +kernel +revert

theorem normalized326 : NormalizationCheck (frozenWangBasis 326) free326 := by
  decide +kernel +revert

theorem checked326 : ∀ k : Fin (2 ^ free326.length), TransitionCheck 326 (unpackCode free326 k.val) (rows326 k) := by
  decide +kernel +revert

theorem normalized327 : NormalizationCheck (frozenWangBasis 327) free327 := by
  decide +kernel +revert

theorem checked327 : ∀ k : Fin (2 ^ free327.length), TransitionCheck 327 (unpackCode free327 k.val) (rows327 k) := by
  decide +kernel +revert

theorem normalized328 : NormalizationCheck (frozenWangBasis 328) free328 := by
  decide +kernel +revert

theorem checked328 : ∀ k : Fin (2 ^ free328.length), TransitionCheck 328 (unpackCode free328 k.val) (rows328 k) := by
  decide +kernel +revert

theorem normalized329 : NormalizationCheck (frozenWangBasis 329) free329 := by
  decide +kernel +revert

theorem checked329 : ∀ k : Fin (2 ^ free329.length), TransitionCheck 329 (unpackCode free329 k.val) (rows329 k) := by
  decide +kernel +revert

theorem normalized330 : NormalizationCheck (frozenWangBasis 330) free330 := by
  decide +kernel +revert

theorem checked330 : ∀ k : Fin (2 ^ free330.length), TransitionCheck 330 (unpackCode free330 k.val) (rows330 k) := by
  decide +kernel +revert

theorem normalized331 : NormalizationCheck (frozenWangBasis 331) free331 := by
  decide +kernel +revert

theorem checked331 : ∀ k : Fin (2 ^ free331.length), TransitionCheck 331 (unpackCode free331 k.val) (rows331 k) := by
  decide +kernel +revert

theorem normalized332 : NormalizationCheck (frozenWangBasis 332) free332 := by
  decide +kernel +revert

theorem checked332 : ∀ k : Fin (2 ^ free332.length), TransitionCheck 332 (unpackCode free332 k.val) (rows332 k) := by
  decide +kernel +revert

theorem normalized333 : NormalizationCheck (frozenWangBasis 333) free333 := by
  decide +kernel +revert

theorem checked333 : ∀ k : Fin (2 ^ free333.length), TransitionCheck 333 (unpackCode free333 k.val) (rows333 k) := by
  decide +kernel +revert

theorem normalized334 : NormalizationCheck (frozenWangBasis 334) free334 := by
  decide +kernel +revert

theorem checked334 : ∀ k : Fin (2 ^ free334.length), TransitionCheck 334 (unpackCode free334 k.val) (rows334 k) := by
  decide +kernel +revert

theorem normalized335 : NormalizationCheck (frozenWangBasis 335) free335 := by
  decide +kernel +revert

theorem checked335 : ∀ k : Fin (2 ^ free335.length), TransitionCheck 335 (unpackCode free335 k.val) (rows335 k) := by
  decide +kernel +revert

theorem covered (j : Fin 16) : ∀ c : Fin 512,
    Covered (spanCodes (c.val :: frozenWangBasis ⟨320 + j.val, by omega⟩)) := by
  fin_cases j
  · exact extensions_of_normalized 320 free320 normalized320 rows320 checked320
  · exact extensions_of_normalized 321 free321 normalized321 rows321 checked321
  · exact extensions_of_normalized 322 free322 normalized322 rows322 checked322
  · exact extensions_of_normalized 323 free323 normalized323 rows323 checked323
  · exact extensions_of_normalized 324 free324 normalized324 rows324 checked324
  · exact extensions_of_normalized 325 free325 normalized325 rows325 checked325
  · exact extensions_of_normalized 326 free326 normalized326 rows326 checked326
  · exact extensions_of_normalized 327 free327 normalized327 rows327 checked327
  · exact extensions_of_normalized 328 free328 normalized328 rows328 checked328
  · exact extensions_of_normalized 329 free329 normalized329 rows329 checked329
  · exact extensions_of_normalized 330 free330 normalized330 rows330 checked330
  · exact extensions_of_normalized 331 free331 normalized331 rows331 checked331
  · exact extensions_of_normalized 332 free332 normalized332 rows332 checked332
  · exact extensions_of_normalized 333 free333 normalized333 rows333 checked333
  · exact extensions_of_normalized 334 free334 normalized334 rows334 checked334
  · exact extensions_of_normalized 335 free335 normalized335 rows335 checked335

end QiushiMatmul.GlobalOrbit.Cases20
