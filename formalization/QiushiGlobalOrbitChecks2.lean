import QiushiGlobalOrbitData2

namespace QiushiMatmul.GlobalOrbit.Cases2
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem normalized32 : NormalizationCheck (frozenWangBasis 32) free32 := by
  decide +kernel +revert

theorem checked32 : ∀ k : Fin (2 ^ free32.length), TransitionCheck 32 (unpackCode free32 k.val) (rows32 k) := by
  decide +kernel +revert

theorem normalized33 : NormalizationCheck (frozenWangBasis 33) free33 := by
  decide +kernel +revert

theorem checked33 : ∀ k : Fin (2 ^ free33.length), TransitionCheck 33 (unpackCode free33 k.val) (rows33 k) := by
  decide +kernel +revert

theorem normalized34 : NormalizationCheck (frozenWangBasis 34) free34 := by
  decide +kernel +revert

theorem checked34 : ∀ k : Fin (2 ^ free34.length), TransitionCheck 34 (unpackCode free34 k.val) (rows34 k) := by
  decide +kernel +revert

theorem normalized35 : NormalizationCheck (frozenWangBasis 35) free35 := by
  decide +kernel +revert

theorem checked35 : ∀ k : Fin (2 ^ free35.length), TransitionCheck 35 (unpackCode free35 k.val) (rows35 k) := by
  decide +kernel +revert

theorem normalized36 : NormalizationCheck (frozenWangBasis 36) free36 := by
  decide +kernel +revert

theorem checked36 : ∀ k : Fin (2 ^ free36.length), TransitionCheck 36 (unpackCode free36 k.val) (rows36 k) := by
  decide +kernel +revert

theorem normalized37 : NormalizationCheck (frozenWangBasis 37) free37 := by
  decide +kernel +revert

theorem checked37 : ∀ k : Fin (2 ^ free37.length), TransitionCheck 37 (unpackCode free37 k.val) (rows37 k) := by
  decide +kernel +revert

theorem normalized38 : NormalizationCheck (frozenWangBasis 38) free38 := by
  decide +kernel +revert

theorem checked38 : ∀ k : Fin (2 ^ free38.length), TransitionCheck 38 (unpackCode free38 k.val) (rows38 k) := by
  decide +kernel +revert

theorem normalized39 : NormalizationCheck (frozenWangBasis 39) free39 := by
  decide +kernel +revert

theorem checked39 : ∀ k : Fin (2 ^ free39.length), TransitionCheck 39 (unpackCode free39 k.val) (rows39 k) := by
  decide +kernel +revert

theorem normalized40 : NormalizationCheck (frozenWangBasis 40) free40 := by
  decide +kernel +revert

theorem checked40 : ∀ k : Fin (2 ^ free40.length), TransitionCheck 40 (unpackCode free40 k.val) (rows40 k) := by
  decide +kernel +revert

theorem normalized41 : NormalizationCheck (frozenWangBasis 41) free41 := by
  decide +kernel +revert

theorem checked41 : ∀ k : Fin (2 ^ free41.length), TransitionCheck 41 (unpackCode free41 k.val) (rows41 k) := by
  decide +kernel +revert

theorem normalized42 : NormalizationCheck (frozenWangBasis 42) free42 := by
  decide +kernel +revert

theorem checked42 : ∀ k : Fin (2 ^ free42.length), TransitionCheck 42 (unpackCode free42 k.val) (rows42 k) := by
  decide +kernel +revert

theorem normalized43 : NormalizationCheck (frozenWangBasis 43) free43 := by
  decide +kernel +revert

theorem checked43 : ∀ k : Fin (2 ^ free43.length), TransitionCheck 43 (unpackCode free43 k.val) (rows43 k) := by
  decide +kernel +revert

theorem normalized44 : NormalizationCheck (frozenWangBasis 44) free44 := by
  decide +kernel +revert

theorem checked44 : ∀ k : Fin (2 ^ free44.length), TransitionCheck 44 (unpackCode free44 k.val) (rows44 k) := by
  decide +kernel +revert

theorem normalized45 : NormalizationCheck (frozenWangBasis 45) free45 := by
  decide +kernel +revert

theorem checked45 : ∀ k : Fin (2 ^ free45.length), TransitionCheck 45 (unpackCode free45 k.val) (rows45 k) := by
  decide +kernel +revert

theorem normalized46 : NormalizationCheck (frozenWangBasis 46) free46 := by
  decide +kernel +revert

theorem checked46 : ∀ k : Fin (2 ^ free46.length), TransitionCheck 46 (unpackCode free46 k.val) (rows46 k) := by
  decide +kernel +revert

theorem normalized47 : NormalizationCheck (frozenWangBasis 47) free47 := by
  decide +kernel +revert

theorem checked47 : ∀ k : Fin (2 ^ free47.length), TransitionCheck 47 (unpackCode free47 k.val) (rows47 k) := by
  decide +kernel +revert

theorem covered (j : Fin 16) : ∀ c : Fin 512,
    Covered (spanCodes (c.val :: frozenWangBasis ⟨32 + j.val, by omega⟩)) := by
  fin_cases j
  · exact extensions_of_normalized 32 free32 normalized32 rows32 checked32
  · exact extensions_of_normalized 33 free33 normalized33 rows33 checked33
  · exact extensions_of_normalized 34 free34 normalized34 rows34 checked34
  · exact extensions_of_normalized 35 free35 normalized35 rows35 checked35
  · exact extensions_of_normalized 36 free36 normalized36 rows36 checked36
  · exact extensions_of_normalized 37 free37 normalized37 rows37 checked37
  · exact extensions_of_normalized 38 free38 normalized38 rows38 checked38
  · exact extensions_of_normalized 39 free39 normalized39 rows39 checked39
  · exact extensions_of_normalized 40 free40 normalized40 rows40 checked40
  · exact extensions_of_normalized 41 free41 normalized41 rows41 checked41
  · exact extensions_of_normalized 42 free42 normalized42 rows42 checked42
  · exact extensions_of_normalized 43 free43 normalized43 rows43 checked43
  · exact extensions_of_normalized 44 free44 normalized44 rows44 checked44
  · exact extensions_of_normalized 45 free45 normalized45 rows45 checked45
  · exact extensions_of_normalized 46 free46 normalized46 rows46 checked46
  · exact extensions_of_normalized 47 free47 normalized47 rows47 checked47

end QiushiMatmul.GlobalOrbit.Cases2
