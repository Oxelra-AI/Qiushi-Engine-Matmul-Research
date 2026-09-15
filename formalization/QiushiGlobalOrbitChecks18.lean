import QiushiGlobalOrbitData18

namespace QiushiMatmul.GlobalOrbit.Cases18
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem normalized288 : NormalizationCheck (frozenWangBasis 288) free288 := by
  decide +kernel +revert

theorem checked288 : ∀ k : Fin (2 ^ free288.length), TransitionCheck 288 (unpackCode free288 k.val) (rows288 k) := by
  decide +kernel +revert

theorem normalized289 : NormalizationCheck (frozenWangBasis 289) free289 := by
  decide +kernel +revert

theorem checked289 : ∀ k : Fin (2 ^ free289.length), TransitionCheck 289 (unpackCode free289 k.val) (rows289 k) := by
  decide +kernel +revert

theorem normalized290 : NormalizationCheck (frozenWangBasis 290) free290 := by
  decide +kernel +revert

theorem checked290 : ∀ k : Fin (2 ^ free290.length), TransitionCheck 290 (unpackCode free290 k.val) (rows290 k) := by
  decide +kernel +revert

theorem normalized291 : NormalizationCheck (frozenWangBasis 291) free291 := by
  decide +kernel +revert

theorem checked291 : ∀ k : Fin (2 ^ free291.length), TransitionCheck 291 (unpackCode free291 k.val) (rows291 k) := by
  decide +kernel +revert

theorem normalized292 : NormalizationCheck (frozenWangBasis 292) free292 := by
  decide +kernel +revert

theorem checked292 : ∀ k : Fin (2 ^ free292.length), TransitionCheck 292 (unpackCode free292 k.val) (rows292 k) := by
  decide +kernel +revert

theorem normalized293 : NormalizationCheck (frozenWangBasis 293) free293 := by
  decide +kernel +revert

theorem checked293 : ∀ k : Fin (2 ^ free293.length), TransitionCheck 293 (unpackCode free293 k.val) (rows293 k) := by
  decide +kernel +revert

theorem normalized294 : NormalizationCheck (frozenWangBasis 294) free294 := by
  decide +kernel +revert

theorem checked294 : ∀ k : Fin (2 ^ free294.length), TransitionCheck 294 (unpackCode free294 k.val) (rows294 k) := by
  decide +kernel +revert

theorem normalized295 : NormalizationCheck (frozenWangBasis 295) free295 := by
  decide +kernel +revert

theorem checked295 : ∀ k : Fin (2 ^ free295.length), TransitionCheck 295 (unpackCode free295 k.val) (rows295 k) := by
  decide +kernel +revert

theorem normalized296 : NormalizationCheck (frozenWangBasis 296) free296 := by
  decide +kernel +revert

theorem checked296 : ∀ k : Fin (2 ^ free296.length), TransitionCheck 296 (unpackCode free296 k.val) (rows296 k) := by
  decide +kernel +revert

theorem normalized297 : NormalizationCheck (frozenWangBasis 297) free297 := by
  decide +kernel +revert

theorem checked297 : ∀ k : Fin (2 ^ free297.length), TransitionCheck 297 (unpackCode free297 k.val) (rows297 k) := by
  decide +kernel +revert

theorem normalized298 : NormalizationCheck (frozenWangBasis 298) free298 := by
  decide +kernel +revert

theorem checked298 : ∀ k : Fin (2 ^ free298.length), TransitionCheck 298 (unpackCode free298 k.val) (rows298 k) := by
  decide +kernel +revert

theorem normalized299 : NormalizationCheck (frozenWangBasis 299) free299 := by
  decide +kernel +revert

theorem checked299 : ∀ k : Fin (2 ^ free299.length), TransitionCheck 299 (unpackCode free299 k.val) (rows299 k) := by
  decide +kernel +revert

theorem normalized300 : NormalizationCheck (frozenWangBasis 300) free300 := by
  decide +kernel +revert

theorem checked300 : ∀ k : Fin (2 ^ free300.length), TransitionCheck 300 (unpackCode free300 k.val) (rows300 k) := by
  decide +kernel +revert

theorem normalized301 : NormalizationCheck (frozenWangBasis 301) free301 := by
  decide +kernel +revert

theorem checked301 : ∀ k : Fin (2 ^ free301.length), TransitionCheck 301 (unpackCode free301 k.val) (rows301 k) := by
  decide +kernel +revert

theorem normalized302 : NormalizationCheck (frozenWangBasis 302) free302 := by
  decide +kernel +revert

theorem checked302 : ∀ k : Fin (2 ^ free302.length), TransitionCheck 302 (unpackCode free302 k.val) (rows302 k) := by
  decide +kernel +revert

theorem normalized303 : NormalizationCheck (frozenWangBasis 303) free303 := by
  decide +kernel +revert

theorem checked303 : ∀ k : Fin (2 ^ free303.length), TransitionCheck 303 (unpackCode free303 k.val) (rows303 k) := by
  decide +kernel +revert

theorem covered (j : Fin 16) : ∀ c : Fin 512,
    Covered (spanCodes (c.val :: frozenWangBasis ⟨288 + j.val, by omega⟩)) := by
  fin_cases j
  · exact extensions_of_normalized 288 free288 normalized288 rows288 checked288
  · exact extensions_of_normalized 289 free289 normalized289 rows289 checked289
  · exact extensions_of_normalized 290 free290 normalized290 rows290 checked290
  · exact extensions_of_normalized 291 free291 normalized291 rows291 checked291
  · exact extensions_of_normalized 292 free292 normalized292 rows292 checked292
  · exact extensions_of_normalized 293 free293 normalized293 rows293 checked293
  · exact extensions_of_normalized 294 free294 normalized294 rows294 checked294
  · exact extensions_of_normalized 295 free295 normalized295 rows295 checked295
  · exact extensions_of_normalized 296 free296 normalized296 rows296 checked296
  · exact extensions_of_normalized 297 free297 normalized297 rows297 checked297
  · exact extensions_of_normalized 298 free298 normalized298 rows298 checked298
  · exact extensions_of_normalized 299 free299 normalized299 rows299 checked299
  · exact extensions_of_normalized 300 free300 normalized300 rows300 checked300
  · exact extensions_of_normalized 301 free301 normalized301 rows301 checked301
  · exact extensions_of_normalized 302 free302 normalized302 rows302 checked302
  · exact extensions_of_normalized 303 free303 normalized303 rows303 checked303

end QiushiMatmul.GlobalOrbit.Cases18
