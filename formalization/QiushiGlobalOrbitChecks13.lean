import QiushiGlobalOrbitData13

namespace QiushiMatmul.GlobalOrbit.Cases13
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem normalized208 : NormalizationCheck (frozenWangBasis 208) free208 := by
  decide +kernel +revert

theorem checked208 : ∀ k : Fin (2 ^ free208.length), TransitionCheck 208 (unpackCode free208 k.val) (rows208 k) := by
  decide +kernel +revert

theorem normalized209 : NormalizationCheck (frozenWangBasis 209) free209 := by
  decide +kernel +revert

theorem checked209 : ∀ k : Fin (2 ^ free209.length), TransitionCheck 209 (unpackCode free209 k.val) (rows209 k) := by
  decide +kernel +revert

theorem normalized210 : NormalizationCheck (frozenWangBasis 210) free210 := by
  decide +kernel +revert

theorem checked210 : ∀ k : Fin (2 ^ free210.length), TransitionCheck 210 (unpackCode free210 k.val) (rows210 k) := by
  decide +kernel +revert

theorem normalized211 : NormalizationCheck (frozenWangBasis 211) free211 := by
  decide +kernel +revert

theorem checked211 : ∀ k : Fin (2 ^ free211.length), TransitionCheck 211 (unpackCode free211 k.val) (rows211 k) := by
  decide +kernel +revert

theorem normalized212 : NormalizationCheck (frozenWangBasis 212) free212 := by
  decide +kernel +revert

theorem checked212 : ∀ k : Fin (2 ^ free212.length), TransitionCheck 212 (unpackCode free212 k.val) (rows212 k) := by
  decide +kernel +revert

theorem normalized213 : NormalizationCheck (frozenWangBasis 213) free213 := by
  decide +kernel +revert

theorem checked213 : ∀ k : Fin (2 ^ free213.length), TransitionCheck 213 (unpackCode free213 k.val) (rows213 k) := by
  decide +kernel +revert

theorem normalized214 : NormalizationCheck (frozenWangBasis 214) free214 := by
  decide +kernel +revert

theorem checked214 : ∀ k : Fin (2 ^ free214.length), TransitionCheck 214 (unpackCode free214 k.val) (rows214 k) := by
  decide +kernel +revert

theorem normalized215 : NormalizationCheck (frozenWangBasis 215) free215 := by
  decide +kernel +revert

theorem checked215 : ∀ k : Fin (2 ^ free215.length), TransitionCheck 215 (unpackCode free215 k.val) (rows215 k) := by
  decide +kernel +revert

theorem normalized216 : NormalizationCheck (frozenWangBasis 216) free216 := by
  decide +kernel +revert

theorem checked216 : ∀ k : Fin (2 ^ free216.length), TransitionCheck 216 (unpackCode free216 k.val) (rows216 k) := by
  decide +kernel +revert

theorem normalized217 : NormalizationCheck (frozenWangBasis 217) free217 := by
  decide +kernel +revert

theorem checked217 : ∀ k : Fin (2 ^ free217.length), TransitionCheck 217 (unpackCode free217 k.val) (rows217 k) := by
  decide +kernel +revert

theorem normalized218 : NormalizationCheck (frozenWangBasis 218) free218 := by
  decide +kernel +revert

theorem checked218 : ∀ k : Fin (2 ^ free218.length), TransitionCheck 218 (unpackCode free218 k.val) (rows218 k) := by
  decide +kernel +revert

theorem normalized219 : NormalizationCheck (frozenWangBasis 219) free219 := by
  decide +kernel +revert

theorem checked219 : ∀ k : Fin (2 ^ free219.length), TransitionCheck 219 (unpackCode free219 k.val) (rows219 k) := by
  decide +kernel +revert

theorem normalized220 : NormalizationCheck (frozenWangBasis 220) free220 := by
  decide +kernel +revert

theorem checked220 : ∀ k : Fin (2 ^ free220.length), TransitionCheck 220 (unpackCode free220 k.val) (rows220 k) := by
  decide +kernel +revert

theorem normalized221 : NormalizationCheck (frozenWangBasis 221) free221 := by
  decide +kernel +revert

theorem checked221 : ∀ k : Fin (2 ^ free221.length), TransitionCheck 221 (unpackCode free221 k.val) (rows221 k) := by
  decide +kernel +revert

theorem normalized222 : NormalizationCheck (frozenWangBasis 222) free222 := by
  decide +kernel +revert

theorem checked222 : ∀ k : Fin (2 ^ free222.length), TransitionCheck 222 (unpackCode free222 k.val) (rows222 k) := by
  decide +kernel +revert

theorem normalized223 : NormalizationCheck (frozenWangBasis 223) free223 := by
  decide +kernel +revert

theorem checked223 : ∀ k : Fin (2 ^ free223.length), TransitionCheck 223 (unpackCode free223 k.val) (rows223 k) := by
  decide +kernel +revert

theorem covered (j : Fin 16) : ∀ c : Fin 512,
    Covered (spanCodes (c.val :: frozenWangBasis ⟨208 + j.val, by omega⟩)) := by
  fin_cases j
  · exact extensions_of_normalized 208 free208 normalized208 rows208 checked208
  · exact extensions_of_normalized 209 free209 normalized209 rows209 checked209
  · exact extensions_of_normalized 210 free210 normalized210 rows210 checked210
  · exact extensions_of_normalized 211 free211 normalized211 rows211 checked211
  · exact extensions_of_normalized 212 free212 normalized212 rows212 checked212
  · exact extensions_of_normalized 213 free213 normalized213 rows213 checked213
  · exact extensions_of_normalized 214 free214 normalized214 rows214 checked214
  · exact extensions_of_normalized 215 free215 normalized215 rows215 checked215
  · exact extensions_of_normalized 216 free216 normalized216 rows216 checked216
  · exact extensions_of_normalized 217 free217 normalized217 rows217 checked217
  · exact extensions_of_normalized 218 free218 normalized218 rows218 checked218
  · exact extensions_of_normalized 219 free219 normalized219 rows219 checked219
  · exact extensions_of_normalized 220 free220 normalized220 rows220 checked220
  · exact extensions_of_normalized 221 free221 normalized221 rows221 checked221
  · exact extensions_of_normalized 222 free222 normalized222 rows222 checked222
  · exact extensions_of_normalized 223 free223 normalized223 rows223 checked223

end QiushiMatmul.GlobalOrbit.Cases13
