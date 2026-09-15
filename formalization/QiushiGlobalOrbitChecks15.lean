import QiushiGlobalOrbitData15

namespace QiushiMatmul.GlobalOrbit.Cases15
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem normalized240 : NormalizationCheck (frozenWangBasis 240) free240 := by
  decide +kernel +revert

theorem checked240 : ∀ k : Fin (2 ^ free240.length), TransitionCheck 240 (unpackCode free240 k.val) (rows240 k) := by
  decide +kernel +revert

theorem normalized241 : NormalizationCheck (frozenWangBasis 241) free241 := by
  decide +kernel +revert

theorem checked241 : ∀ k : Fin (2 ^ free241.length), TransitionCheck 241 (unpackCode free241 k.val) (rows241 k) := by
  decide +kernel +revert

theorem normalized242 : NormalizationCheck (frozenWangBasis 242) free242 := by
  decide +kernel +revert

theorem checked242 : ∀ k : Fin (2 ^ free242.length), TransitionCheck 242 (unpackCode free242 k.val) (rows242 k) := by
  decide +kernel +revert

theorem normalized243 : NormalizationCheck (frozenWangBasis 243) free243 := by
  decide +kernel +revert

theorem checked243 : ∀ k : Fin (2 ^ free243.length), TransitionCheck 243 (unpackCode free243 k.val) (rows243 k) := by
  decide +kernel +revert

theorem normalized244 : NormalizationCheck (frozenWangBasis 244) free244 := by
  decide +kernel +revert

theorem checked244 : ∀ k : Fin (2 ^ free244.length), TransitionCheck 244 (unpackCode free244 k.val) (rows244 k) := by
  decide +kernel +revert

theorem normalized245 : NormalizationCheck (frozenWangBasis 245) free245 := by
  decide +kernel +revert

theorem checked245 : ∀ k : Fin (2 ^ free245.length), TransitionCheck 245 (unpackCode free245 k.val) (rows245 k) := by
  decide +kernel +revert

theorem normalized246 : NormalizationCheck (frozenWangBasis 246) free246 := by
  decide +kernel +revert

theorem checked246 : ∀ k : Fin (2 ^ free246.length), TransitionCheck 246 (unpackCode free246 k.val) (rows246 k) := by
  decide +kernel +revert

theorem normalized247 : NormalizationCheck (frozenWangBasis 247) free247 := by
  decide +kernel +revert

theorem checked247 : ∀ k : Fin (2 ^ free247.length), TransitionCheck 247 (unpackCode free247 k.val) (rows247 k) := by
  decide +kernel +revert

theorem normalized248 : NormalizationCheck (frozenWangBasis 248) free248 := by
  decide +kernel +revert

theorem checked248 : ∀ k : Fin (2 ^ free248.length), TransitionCheck 248 (unpackCode free248 k.val) (rows248 k) := by
  decide +kernel +revert

theorem normalized249 : NormalizationCheck (frozenWangBasis 249) free249 := by
  decide +kernel +revert

theorem checked249 : ∀ k : Fin (2 ^ free249.length), TransitionCheck 249 (unpackCode free249 k.val) (rows249 k) := by
  decide +kernel +revert

theorem normalized250 : NormalizationCheck (frozenWangBasis 250) free250 := by
  decide +kernel +revert

theorem checked250 : ∀ k : Fin (2 ^ free250.length), TransitionCheck 250 (unpackCode free250 k.val) (rows250 k) := by
  decide +kernel +revert

theorem normalized251 : NormalizationCheck (frozenWangBasis 251) free251 := by
  decide +kernel +revert

theorem checked251 : ∀ k : Fin (2 ^ free251.length), TransitionCheck 251 (unpackCode free251 k.val) (rows251 k) := by
  decide +kernel +revert

theorem normalized252 : NormalizationCheck (frozenWangBasis 252) free252 := by
  decide +kernel +revert

theorem checked252 : ∀ k : Fin (2 ^ free252.length), TransitionCheck 252 (unpackCode free252 k.val) (rows252 k) := by
  decide +kernel +revert

theorem normalized253 : NormalizationCheck (frozenWangBasis 253) free253 := by
  decide +kernel +revert

theorem checked253 : ∀ k : Fin (2 ^ free253.length), TransitionCheck 253 (unpackCode free253 k.val) (rows253 k) := by
  decide +kernel +revert

theorem normalized254 : NormalizationCheck (frozenWangBasis 254) free254 := by
  decide +kernel +revert

theorem checked254 : ∀ k : Fin (2 ^ free254.length), TransitionCheck 254 (unpackCode free254 k.val) (rows254 k) := by
  decide +kernel +revert

theorem normalized255 : NormalizationCheck (frozenWangBasis 255) free255 := by
  decide +kernel +revert

theorem checked255 : ∀ k : Fin (2 ^ free255.length), TransitionCheck 255 (unpackCode free255 k.val) (rows255 k) := by
  decide +kernel +revert

theorem covered (j : Fin 16) : ∀ c : Fin 512,
    Covered (spanCodes (c.val :: frozenWangBasis ⟨240 + j.val, by omega⟩)) := by
  fin_cases j
  · exact extensions_of_normalized 240 free240 normalized240 rows240 checked240
  · exact extensions_of_normalized 241 free241 normalized241 rows241 checked241
  · exact extensions_of_normalized 242 free242 normalized242 rows242 checked242
  · exact extensions_of_normalized 243 free243 normalized243 rows243 checked243
  · exact extensions_of_normalized 244 free244 normalized244 rows244 checked244
  · exact extensions_of_normalized 245 free245 normalized245 rows245 checked245
  · exact extensions_of_normalized 246 free246 normalized246 rows246 checked246
  · exact extensions_of_normalized 247 free247 normalized247 rows247 checked247
  · exact extensions_of_normalized 248 free248 normalized248 rows248 checked248
  · exact extensions_of_normalized 249 free249 normalized249 rows249 checked249
  · exact extensions_of_normalized 250 free250 normalized250 rows250 checked250
  · exact extensions_of_normalized 251 free251 normalized251 rows251 checked251
  · exact extensions_of_normalized 252 free252 normalized252 rows252 checked252
  · exact extensions_of_normalized 253 free253 normalized253 rows253 checked253
  · exact extensions_of_normalized 254 free254 normalized254 rows254 checked254
  · exact extensions_of_normalized 255 free255 normalized255 rows255 checked255

end QiushiMatmul.GlobalOrbit.Cases15
