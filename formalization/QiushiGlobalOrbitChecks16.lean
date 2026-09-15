import QiushiGlobalOrbitData16

namespace QiushiMatmul.GlobalOrbit.Cases16
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem normalized256 : NormalizationCheck (frozenWangBasis 256) free256 := by
  decide +kernel +revert

theorem checked256 : ∀ k : Fin (2 ^ free256.length), TransitionCheck 256 (unpackCode free256 k.val) (rows256 k) := by
  decide +kernel +revert

theorem normalized257 : NormalizationCheck (frozenWangBasis 257) free257 := by
  decide +kernel +revert

theorem checked257 : ∀ k : Fin (2 ^ free257.length), TransitionCheck 257 (unpackCode free257 k.val) (rows257 k) := by
  decide +kernel +revert

theorem normalized258 : NormalizationCheck (frozenWangBasis 258) free258 := by
  decide +kernel +revert

theorem checked258 : ∀ k : Fin (2 ^ free258.length), TransitionCheck 258 (unpackCode free258 k.val) (rows258 k) := by
  decide +kernel +revert

theorem normalized259 : NormalizationCheck (frozenWangBasis 259) free259 := by
  decide +kernel +revert

theorem checked259 : ∀ k : Fin (2 ^ free259.length), TransitionCheck 259 (unpackCode free259 k.val) (rows259 k) := by
  decide +kernel +revert

theorem normalized260 : NormalizationCheck (frozenWangBasis 260) free260 := by
  decide +kernel +revert

theorem checked260 : ∀ k : Fin (2 ^ free260.length), TransitionCheck 260 (unpackCode free260 k.val) (rows260 k) := by
  decide +kernel +revert

theorem normalized261 : NormalizationCheck (frozenWangBasis 261) free261 := by
  decide +kernel +revert

theorem checked261 : ∀ k : Fin (2 ^ free261.length), TransitionCheck 261 (unpackCode free261 k.val) (rows261 k) := by
  decide +kernel +revert

theorem normalized262 : NormalizationCheck (frozenWangBasis 262) free262 := by
  decide +kernel +revert

theorem checked262 : ∀ k : Fin (2 ^ free262.length), TransitionCheck 262 (unpackCode free262 k.val) (rows262 k) := by
  decide +kernel +revert

theorem normalized263 : NormalizationCheck (frozenWangBasis 263) free263 := by
  decide +kernel +revert

theorem checked263 : ∀ k : Fin (2 ^ free263.length), TransitionCheck 263 (unpackCode free263 k.val) (rows263 k) := by
  decide +kernel +revert

theorem normalized264 : NormalizationCheck (frozenWangBasis 264) free264 := by
  decide +kernel +revert

theorem checked264 : ∀ k : Fin (2 ^ free264.length), TransitionCheck 264 (unpackCode free264 k.val) (rows264 k) := by
  decide +kernel +revert

theorem normalized265 : NormalizationCheck (frozenWangBasis 265) free265 := by
  decide +kernel +revert

theorem checked265 : ∀ k : Fin (2 ^ free265.length), TransitionCheck 265 (unpackCode free265 k.val) (rows265 k) := by
  decide +kernel +revert

theorem normalized266 : NormalizationCheck (frozenWangBasis 266) free266 := by
  decide +kernel +revert

theorem checked266 : ∀ k : Fin (2 ^ free266.length), TransitionCheck 266 (unpackCode free266 k.val) (rows266 k) := by
  decide +kernel +revert

theorem normalized267 : NormalizationCheck (frozenWangBasis 267) free267 := by
  decide +kernel +revert

theorem checked267 : ∀ k : Fin (2 ^ free267.length), TransitionCheck 267 (unpackCode free267 k.val) (rows267 k) := by
  decide +kernel +revert

theorem normalized268 : NormalizationCheck (frozenWangBasis 268) free268 := by
  decide +kernel +revert

theorem checked268 : ∀ k : Fin (2 ^ free268.length), TransitionCheck 268 (unpackCode free268 k.val) (rows268 k) := by
  decide +kernel +revert

theorem normalized269 : NormalizationCheck (frozenWangBasis 269) free269 := by
  decide +kernel +revert

theorem checked269 : ∀ k : Fin (2 ^ free269.length), TransitionCheck 269 (unpackCode free269 k.val) (rows269 k) := by
  decide +kernel +revert

theorem normalized270 : NormalizationCheck (frozenWangBasis 270) free270 := by
  decide +kernel +revert

theorem checked270 : ∀ k : Fin (2 ^ free270.length), TransitionCheck 270 (unpackCode free270 k.val) (rows270 k) := by
  decide +kernel +revert

theorem normalized271 : NormalizationCheck (frozenWangBasis 271) free271 := by
  decide +kernel +revert

theorem checked271 : ∀ k : Fin (2 ^ free271.length), TransitionCheck 271 (unpackCode free271 k.val) (rows271 k) := by
  decide +kernel +revert

theorem covered (j : Fin 16) : ∀ c : Fin 512,
    Covered (spanCodes (c.val :: frozenWangBasis ⟨256 + j.val, by omega⟩)) := by
  fin_cases j
  · exact extensions_of_normalized 256 free256 normalized256 rows256 checked256
  · exact extensions_of_normalized 257 free257 normalized257 rows257 checked257
  · exact extensions_of_normalized 258 free258 normalized258 rows258 checked258
  · exact extensions_of_normalized 259 free259 normalized259 rows259 checked259
  · exact extensions_of_normalized 260 free260 normalized260 rows260 checked260
  · exact extensions_of_normalized 261 free261 normalized261 rows261 checked261
  · exact extensions_of_normalized 262 free262 normalized262 rows262 checked262
  · exact extensions_of_normalized 263 free263 normalized263 rows263 checked263
  · exact extensions_of_normalized 264 free264 normalized264 rows264 checked264
  · exact extensions_of_normalized 265 free265 normalized265 rows265 checked265
  · exact extensions_of_normalized 266 free266 normalized266 rows266 checked266
  · exact extensions_of_normalized 267 free267 normalized267 rows267 checked267
  · exact extensions_of_normalized 268 free268 normalized268 rows268 checked268
  · exact extensions_of_normalized 269 free269 normalized269 rows269 checked269
  · exact extensions_of_normalized 270 free270 normalized270 rows270 checked270
  · exact extensions_of_normalized 271 free271 normalized271 rows271 checked271

end QiushiMatmul.GlobalOrbit.Cases16
