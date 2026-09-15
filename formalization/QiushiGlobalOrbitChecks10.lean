import QiushiGlobalOrbitData10

namespace QiushiMatmul.GlobalOrbit.Cases10
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem normalized160 : NormalizationCheck (frozenWangBasis 160) free160 := by
  decide +kernel +revert

theorem checked160 : ∀ k : Fin (2 ^ free160.length), TransitionCheck 160 (unpackCode free160 k.val) (rows160 k) := by
  decide +kernel +revert

theorem normalized161 : NormalizationCheck (frozenWangBasis 161) free161 := by
  decide +kernel +revert

theorem checked161 : ∀ k : Fin (2 ^ free161.length), TransitionCheck 161 (unpackCode free161 k.val) (rows161 k) := by
  decide +kernel +revert

theorem normalized162 : NormalizationCheck (frozenWangBasis 162) free162 := by
  decide +kernel +revert

theorem checked162 : ∀ k : Fin (2 ^ free162.length), TransitionCheck 162 (unpackCode free162 k.val) (rows162 k) := by
  decide +kernel +revert

theorem normalized163 : NormalizationCheck (frozenWangBasis 163) free163 := by
  decide +kernel +revert

theorem checked163 : ∀ k : Fin (2 ^ free163.length), TransitionCheck 163 (unpackCode free163 k.val) (rows163 k) := by
  decide +kernel +revert

theorem normalized164 : NormalizationCheck (frozenWangBasis 164) free164 := by
  decide +kernel +revert

theorem checked164 : ∀ k : Fin (2 ^ free164.length), TransitionCheck 164 (unpackCode free164 k.val) (rows164 k) := by
  decide +kernel +revert

theorem normalized165 : NormalizationCheck (frozenWangBasis 165) free165 := by
  decide +kernel +revert

theorem checked165 : ∀ k : Fin (2 ^ free165.length), TransitionCheck 165 (unpackCode free165 k.val) (rows165 k) := by
  decide +kernel +revert

theorem normalized166 : NormalizationCheck (frozenWangBasis 166) free166 := by
  decide +kernel +revert

theorem checked166 : ∀ k : Fin (2 ^ free166.length), TransitionCheck 166 (unpackCode free166 k.val) (rows166 k) := by
  decide +kernel +revert

theorem normalized167 : NormalizationCheck (frozenWangBasis 167) free167 := by
  decide +kernel +revert

theorem checked167 : ∀ k : Fin (2 ^ free167.length), TransitionCheck 167 (unpackCode free167 k.val) (rows167 k) := by
  decide +kernel +revert

theorem normalized168 : NormalizationCheck (frozenWangBasis 168) free168 := by
  decide +kernel +revert

theorem checked168 : ∀ k : Fin (2 ^ free168.length), TransitionCheck 168 (unpackCode free168 k.val) (rows168 k) := by
  decide +kernel +revert

theorem normalized169 : NormalizationCheck (frozenWangBasis 169) free169 := by
  decide +kernel +revert

theorem checked169 : ∀ k : Fin (2 ^ free169.length), TransitionCheck 169 (unpackCode free169 k.val) (rows169 k) := by
  decide +kernel +revert

theorem normalized170 : NormalizationCheck (frozenWangBasis 170) free170 := by
  decide +kernel +revert

theorem checked170 : ∀ k : Fin (2 ^ free170.length), TransitionCheck 170 (unpackCode free170 k.val) (rows170 k) := by
  decide +kernel +revert

theorem normalized171 : NormalizationCheck (frozenWangBasis 171) free171 := by
  decide +kernel +revert

theorem checked171 : ∀ k : Fin (2 ^ free171.length), TransitionCheck 171 (unpackCode free171 k.val) (rows171 k) := by
  decide +kernel +revert

theorem normalized172 : NormalizationCheck (frozenWangBasis 172) free172 := by
  decide +kernel +revert

theorem checked172 : ∀ k : Fin (2 ^ free172.length), TransitionCheck 172 (unpackCode free172 k.val) (rows172 k) := by
  decide +kernel +revert

theorem normalized173 : NormalizationCheck (frozenWangBasis 173) free173 := by
  decide +kernel +revert

theorem checked173 : ∀ k : Fin (2 ^ free173.length), TransitionCheck 173 (unpackCode free173 k.val) (rows173 k) := by
  decide +kernel +revert

theorem normalized174 : NormalizationCheck (frozenWangBasis 174) free174 := by
  decide +kernel +revert

theorem checked174 : ∀ k : Fin (2 ^ free174.length), TransitionCheck 174 (unpackCode free174 k.val) (rows174 k) := by
  decide +kernel +revert

theorem normalized175 : NormalizationCheck (frozenWangBasis 175) free175 := by
  decide +kernel +revert

theorem checked175 : ∀ k : Fin (2 ^ free175.length), TransitionCheck 175 (unpackCode free175 k.val) (rows175 k) := by
  decide +kernel +revert

theorem covered (j : Fin 16) : ∀ c : Fin 512,
    Covered (spanCodes (c.val :: frozenWangBasis ⟨160 + j.val, by omega⟩)) := by
  fin_cases j
  · exact extensions_of_normalized 160 free160 normalized160 rows160 checked160
  · exact extensions_of_normalized 161 free161 normalized161 rows161 checked161
  · exact extensions_of_normalized 162 free162 normalized162 rows162 checked162
  · exact extensions_of_normalized 163 free163 normalized163 rows163 checked163
  · exact extensions_of_normalized 164 free164 normalized164 rows164 checked164
  · exact extensions_of_normalized 165 free165 normalized165 rows165 checked165
  · exact extensions_of_normalized 166 free166 normalized166 rows166 checked166
  · exact extensions_of_normalized 167 free167 normalized167 rows167 checked167
  · exact extensions_of_normalized 168 free168 normalized168 rows168 checked168
  · exact extensions_of_normalized 169 free169 normalized169 rows169 checked169
  · exact extensions_of_normalized 170 free170 normalized170 rows170 checked170
  · exact extensions_of_normalized 171 free171 normalized171 rows171 checked171
  · exact extensions_of_normalized 172 free172 normalized172 rows172 checked172
  · exact extensions_of_normalized 173 free173 normalized173 rows173 checked173
  · exact extensions_of_normalized 174 free174 normalized174 rows174 checked174
  · exact extensions_of_normalized 175 free175 normalized175 rows175 checked175

end QiushiMatmul.GlobalOrbit.Cases10
