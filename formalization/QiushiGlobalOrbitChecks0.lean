import QiushiGlobalOrbitData0

namespace QiushiMatmul.GlobalOrbit.Cases0
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem normalized0 : NormalizationCheck (frozenWangBasis 0) free0 := by
  decide +kernel +revert

theorem checked0 : ∀ k : Fin (2 ^ free0.length), TransitionCheck 0 (unpackCode free0 k.val) (rows0 k) := by
  decide +kernel +revert

theorem normalized1 : NormalizationCheck (frozenWangBasis 1) free1 := by
  decide +kernel +revert

theorem checked1 : ∀ k : Fin (2 ^ free1.length), TransitionCheck 1 (unpackCode free1 k.val) (rows1 k) := by
  decide +kernel +revert

theorem normalized2 : NormalizationCheck (frozenWangBasis 2) free2 := by
  decide +kernel +revert

theorem checked2 : ∀ k : Fin (2 ^ free2.length), TransitionCheck 2 (unpackCode free2 k.val) (rows2 k) := by
  decide +kernel +revert

theorem normalized3 : NormalizationCheck (frozenWangBasis 3) free3 := by
  decide +kernel +revert

theorem checked3 : ∀ k : Fin (2 ^ free3.length), TransitionCheck 3 (unpackCode free3 k.val) (rows3 k) := by
  decide +kernel +revert

theorem normalized4 : NormalizationCheck (frozenWangBasis 4) free4 := by
  decide +kernel +revert

theorem checked4 : ∀ k : Fin (2 ^ free4.length), TransitionCheck 4 (unpackCode free4 k.val) (rows4 k) := by
  decide +kernel +revert

theorem normalized5 : NormalizationCheck (frozenWangBasis 5) free5 := by
  decide +kernel +revert

theorem checked5 : ∀ k : Fin (2 ^ free5.length), TransitionCheck 5 (unpackCode free5 k.val) (rows5 k) := by
  decide +kernel +revert

theorem normalized6 : NormalizationCheck (frozenWangBasis 6) free6 := by
  decide +kernel +revert

theorem checked6 : ∀ k : Fin (2 ^ free6.length), TransitionCheck 6 (unpackCode free6 k.val) (rows6 k) := by
  decide +kernel +revert

theorem normalized7 : NormalizationCheck (frozenWangBasis 7) free7 := by
  decide +kernel +revert

theorem checked7 : ∀ k : Fin (2 ^ free7.length), TransitionCheck 7 (unpackCode free7 k.val) (rows7 k) := by
  decide +kernel +revert

theorem normalized8 : NormalizationCheck (frozenWangBasis 8) free8 := by
  decide +kernel +revert

theorem checked8 : ∀ k : Fin (2 ^ free8.length), TransitionCheck 8 (unpackCode free8 k.val) (rows8 k) := by
  decide +kernel +revert

theorem normalized9 : NormalizationCheck (frozenWangBasis 9) free9 := by
  decide +kernel +revert

theorem checked9 : ∀ k : Fin (2 ^ free9.length), TransitionCheck 9 (unpackCode free9 k.val) (rows9 k) := by
  decide +kernel +revert

theorem normalized10 : NormalizationCheck (frozenWangBasis 10) free10 := by
  decide +kernel +revert

theorem checked10 : ∀ k : Fin (2 ^ free10.length), TransitionCheck 10 (unpackCode free10 k.val) (rows10 k) := by
  decide +kernel +revert

theorem normalized11 : NormalizationCheck (frozenWangBasis 11) free11 := by
  decide +kernel +revert

theorem checked11 : ∀ k : Fin (2 ^ free11.length), TransitionCheck 11 (unpackCode free11 k.val) (rows11 k) := by
  decide +kernel +revert

theorem normalized12 : NormalizationCheck (frozenWangBasis 12) free12 := by
  decide +kernel +revert

theorem checked12 : ∀ k : Fin (2 ^ free12.length), TransitionCheck 12 (unpackCode free12 k.val) (rows12 k) := by
  decide +kernel +revert

theorem normalized13 : NormalizationCheck (frozenWangBasis 13) free13 := by
  decide +kernel +revert

theorem checked13 : ∀ k : Fin (2 ^ free13.length), TransitionCheck 13 (unpackCode free13 k.val) (rows13 k) := by
  decide +kernel +revert

theorem normalized14 : NormalizationCheck (frozenWangBasis 14) free14 := by
  decide +kernel +revert

theorem checked14 : ∀ k : Fin (2 ^ free14.length), TransitionCheck 14 (unpackCode free14 k.val) (rows14 k) := by
  decide +kernel +revert

theorem normalized15 : NormalizationCheck (frozenWangBasis 15) free15 := by
  decide +kernel +revert

theorem checked15 : ∀ k : Fin (2 ^ free15.length), TransitionCheck 15 (unpackCode free15 k.val) (rows15 k) := by
  decide +kernel +revert

theorem covered (j : Fin 16) : ∀ c : Fin 512,
    Covered (spanCodes (c.val :: frozenWangBasis ⟨0 + j.val, by omega⟩)) := by
  fin_cases j
  · exact extensions_of_normalized 0 free0 normalized0 rows0 checked0
  · exact extensions_of_normalized 1 free1 normalized1 rows1 checked1
  · exact extensions_of_normalized 2 free2 normalized2 rows2 checked2
  · exact extensions_of_normalized 3 free3 normalized3 rows3 checked3
  · exact extensions_of_normalized 4 free4 normalized4 rows4 checked4
  · exact extensions_of_normalized 5 free5 normalized5 rows5 checked5
  · exact extensions_of_normalized 6 free6 normalized6 rows6 checked6
  · exact extensions_of_normalized 7 free7 normalized7 rows7 checked7
  · exact extensions_of_normalized 8 free8 normalized8 rows8 checked8
  · exact extensions_of_normalized 9 free9 normalized9 rows9 checked9
  · exact extensions_of_normalized 10 free10 normalized10 rows10 checked10
  · exact extensions_of_normalized 11 free11 normalized11 rows11 checked11
  · exact extensions_of_normalized 12 free12 normalized12 rows12 checked12
  · exact extensions_of_normalized 13 free13 normalized13 rows13 checked13
  · exact extensions_of_normalized 14 free14 normalized14 rows14 checked14
  · exact extensions_of_normalized 15 free15 normalized15 rows15 checked15

end QiushiMatmul.GlobalOrbit.Cases0
