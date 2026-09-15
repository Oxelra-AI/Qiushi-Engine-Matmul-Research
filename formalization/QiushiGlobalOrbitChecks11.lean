import QiushiGlobalOrbitData11

namespace QiushiMatmul.GlobalOrbit.Cases11
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem normalized176 : NormalizationCheck (frozenWangBasis 176) free176 := by
  decide +kernel +revert

theorem checked176 : ∀ k : Fin (2 ^ free176.length), TransitionCheck 176 (unpackCode free176 k.val) (rows176 k) := by
  decide +kernel +revert

theorem normalized177 : NormalizationCheck (frozenWangBasis 177) free177 := by
  decide +kernel +revert

theorem checked177 : ∀ k : Fin (2 ^ free177.length), TransitionCheck 177 (unpackCode free177 k.val) (rows177 k) := by
  decide +kernel +revert

theorem normalized178 : NormalizationCheck (frozenWangBasis 178) free178 := by
  decide +kernel +revert

theorem checked178 : ∀ k : Fin (2 ^ free178.length), TransitionCheck 178 (unpackCode free178 k.val) (rows178 k) := by
  decide +kernel +revert

theorem normalized179 : NormalizationCheck (frozenWangBasis 179) free179 := by
  decide +kernel +revert

theorem checked179 : ∀ k : Fin (2 ^ free179.length), TransitionCheck 179 (unpackCode free179 k.val) (rows179 k) := by
  decide +kernel +revert

theorem normalized180 : NormalizationCheck (frozenWangBasis 180) free180 := by
  decide +kernel +revert

theorem checked180 : ∀ k : Fin (2 ^ free180.length), TransitionCheck 180 (unpackCode free180 k.val) (rows180 k) := by
  decide +kernel +revert

theorem normalized181 : NormalizationCheck (frozenWangBasis 181) free181 := by
  decide +kernel +revert

theorem checked181 : ∀ k : Fin (2 ^ free181.length), TransitionCheck 181 (unpackCode free181 k.val) (rows181 k) := by
  decide +kernel +revert

theorem normalized182 : NormalizationCheck (frozenWangBasis 182) free182 := by
  decide +kernel +revert

theorem checked182 : ∀ k : Fin (2 ^ free182.length), TransitionCheck 182 (unpackCode free182 k.val) (rows182 k) := by
  decide +kernel +revert

theorem normalized183 : NormalizationCheck (frozenWangBasis 183) free183 := by
  decide +kernel +revert

theorem checked183 : ∀ k : Fin (2 ^ free183.length), TransitionCheck 183 (unpackCode free183 k.val) (rows183 k) := by
  decide +kernel +revert

theorem normalized184 : NormalizationCheck (frozenWangBasis 184) free184 := by
  decide +kernel +revert

theorem checked184 : ∀ k : Fin (2 ^ free184.length), TransitionCheck 184 (unpackCode free184 k.val) (rows184 k) := by
  decide +kernel +revert

theorem normalized185 : NormalizationCheck (frozenWangBasis 185) free185 := by
  decide +kernel +revert

theorem checked185 : ∀ k : Fin (2 ^ free185.length), TransitionCheck 185 (unpackCode free185 k.val) (rows185 k) := by
  decide +kernel +revert

theorem normalized186 : NormalizationCheck (frozenWangBasis 186) free186 := by
  decide +kernel +revert

theorem checked186 : ∀ k : Fin (2 ^ free186.length), TransitionCheck 186 (unpackCode free186 k.val) (rows186 k) := by
  decide +kernel +revert

theorem normalized187 : NormalizationCheck (frozenWangBasis 187) free187 := by
  decide +kernel +revert

theorem checked187 : ∀ k : Fin (2 ^ free187.length), TransitionCheck 187 (unpackCode free187 k.val) (rows187 k) := by
  decide +kernel +revert

theorem normalized188 : NormalizationCheck (frozenWangBasis 188) free188 := by
  decide +kernel +revert

theorem checked188 : ∀ k : Fin (2 ^ free188.length), TransitionCheck 188 (unpackCode free188 k.val) (rows188 k) := by
  decide +kernel +revert

theorem normalized189 : NormalizationCheck (frozenWangBasis 189) free189 := by
  decide +kernel +revert

theorem checked189 : ∀ k : Fin (2 ^ free189.length), TransitionCheck 189 (unpackCode free189 k.val) (rows189 k) := by
  decide +kernel +revert

theorem normalized190 : NormalizationCheck (frozenWangBasis 190) free190 := by
  decide +kernel +revert

theorem checked190 : ∀ k : Fin (2 ^ free190.length), TransitionCheck 190 (unpackCode free190 k.val) (rows190 k) := by
  decide +kernel +revert

theorem normalized191 : NormalizationCheck (frozenWangBasis 191) free191 := by
  decide +kernel +revert

theorem checked191 : ∀ k : Fin (2 ^ free191.length), TransitionCheck 191 (unpackCode free191 k.val) (rows191 k) := by
  decide +kernel +revert

theorem covered (j : Fin 16) : ∀ c : Fin 512,
    Covered (spanCodes (c.val :: frozenWangBasis ⟨176 + j.val, by omega⟩)) := by
  fin_cases j
  · exact extensions_of_normalized 176 free176 normalized176 rows176 checked176
  · exact extensions_of_normalized 177 free177 normalized177 rows177 checked177
  · exact extensions_of_normalized 178 free178 normalized178 rows178 checked178
  · exact extensions_of_normalized 179 free179 normalized179 rows179 checked179
  · exact extensions_of_normalized 180 free180 normalized180 rows180 checked180
  · exact extensions_of_normalized 181 free181 normalized181 rows181 checked181
  · exact extensions_of_normalized 182 free182 normalized182 rows182 checked182
  · exact extensions_of_normalized 183 free183 normalized183 rows183 checked183
  · exact extensions_of_normalized 184 free184 normalized184 rows184 checked184
  · exact extensions_of_normalized 185 free185 normalized185 rows185 checked185
  · exact extensions_of_normalized 186 free186 normalized186 rows186 checked186
  · exact extensions_of_normalized 187 free187 normalized187 rows187 checked187
  · exact extensions_of_normalized 188 free188 normalized188 rows188 checked188
  · exact extensions_of_normalized 189 free189 normalized189 rows189 checked189
  · exact extensions_of_normalized 190 free190 normalized190 rows190 checked190
  · exact extensions_of_normalized 191 free191 normalized191 rows191 checked191

end QiushiMatmul.GlobalOrbit.Cases11
