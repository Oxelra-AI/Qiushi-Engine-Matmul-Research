import QiushiGlobalOrbitData1

namespace QiushiMatmul.GlobalOrbit.Cases1
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem normalized16 : NormalizationCheck (frozenWangBasis 16) free16 := by
  decide +kernel +revert

theorem checked16 : ∀ k : Fin (2 ^ free16.length), TransitionCheck 16 (unpackCode free16 k.val) (rows16 k) := by
  decide +kernel +revert

theorem normalized17 : NormalizationCheck (frozenWangBasis 17) free17 := by
  decide +kernel +revert

theorem checked17 : ∀ k : Fin (2 ^ free17.length), TransitionCheck 17 (unpackCode free17 k.val) (rows17 k) := by
  decide +kernel +revert

theorem normalized18 : NormalizationCheck (frozenWangBasis 18) free18 := by
  decide +kernel +revert

theorem checked18 : ∀ k : Fin (2 ^ free18.length), TransitionCheck 18 (unpackCode free18 k.val) (rows18 k) := by
  decide +kernel +revert

theorem normalized19 : NormalizationCheck (frozenWangBasis 19) free19 := by
  decide +kernel +revert

theorem checked19 : ∀ k : Fin (2 ^ free19.length), TransitionCheck 19 (unpackCode free19 k.val) (rows19 k) := by
  decide +kernel +revert

theorem normalized20 : NormalizationCheck (frozenWangBasis 20) free20 := by
  decide +kernel +revert

theorem checked20 : ∀ k : Fin (2 ^ free20.length), TransitionCheck 20 (unpackCode free20 k.val) (rows20 k) := by
  decide +kernel +revert

theorem normalized21 : NormalizationCheck (frozenWangBasis 21) free21 := by
  decide +kernel +revert

theorem checked21 : ∀ k : Fin (2 ^ free21.length), TransitionCheck 21 (unpackCode free21 k.val) (rows21 k) := by
  decide +kernel +revert

theorem normalized22 : NormalizationCheck (frozenWangBasis 22) free22 := by
  decide +kernel +revert

theorem checked22 : ∀ k : Fin (2 ^ free22.length), TransitionCheck 22 (unpackCode free22 k.val) (rows22 k) := by
  decide +kernel +revert

theorem normalized23 : NormalizationCheck (frozenWangBasis 23) free23 := by
  decide +kernel +revert

theorem checked23 : ∀ k : Fin (2 ^ free23.length), TransitionCheck 23 (unpackCode free23 k.val) (rows23 k) := by
  decide +kernel +revert

theorem normalized24 : NormalizationCheck (frozenWangBasis 24) free24 := by
  decide +kernel +revert

theorem checked24 : ∀ k : Fin (2 ^ free24.length), TransitionCheck 24 (unpackCode free24 k.val) (rows24 k) := by
  decide +kernel +revert

theorem normalized25 : NormalizationCheck (frozenWangBasis 25) free25 := by
  decide +kernel +revert

theorem checked25 : ∀ k : Fin (2 ^ free25.length), TransitionCheck 25 (unpackCode free25 k.val) (rows25 k) := by
  decide +kernel +revert

theorem normalized26 : NormalizationCheck (frozenWangBasis 26) free26 := by
  decide +kernel +revert

theorem checked26 : ∀ k : Fin (2 ^ free26.length), TransitionCheck 26 (unpackCode free26 k.val) (rows26 k) := by
  decide +kernel +revert

theorem normalized27 : NormalizationCheck (frozenWangBasis 27) free27 := by
  decide +kernel +revert

theorem checked27 : ∀ k : Fin (2 ^ free27.length), TransitionCheck 27 (unpackCode free27 k.val) (rows27 k) := by
  decide +kernel +revert

theorem normalized28 : NormalizationCheck (frozenWangBasis 28) free28 := by
  decide +kernel +revert

theorem checked28 : ∀ k : Fin (2 ^ free28.length), TransitionCheck 28 (unpackCode free28 k.val) (rows28 k) := by
  decide +kernel +revert

theorem normalized29 : NormalizationCheck (frozenWangBasis 29) free29 := by
  decide +kernel +revert

theorem checked29 : ∀ k : Fin (2 ^ free29.length), TransitionCheck 29 (unpackCode free29 k.val) (rows29 k) := by
  decide +kernel +revert

theorem normalized30 : NormalizationCheck (frozenWangBasis 30) free30 := by
  decide +kernel +revert

theorem checked30 : ∀ k : Fin (2 ^ free30.length), TransitionCheck 30 (unpackCode free30 k.val) (rows30 k) := by
  decide +kernel +revert

theorem normalized31 : NormalizationCheck (frozenWangBasis 31) free31 := by
  decide +kernel +revert

theorem checked31 : ∀ k : Fin (2 ^ free31.length), TransitionCheck 31 (unpackCode free31 k.val) (rows31 k) := by
  decide +kernel +revert

theorem covered (j : Fin 16) : ∀ c : Fin 512,
    Covered (spanCodes (c.val :: frozenWangBasis ⟨16 + j.val, by omega⟩)) := by
  fin_cases j
  · exact extensions_of_normalized 16 free16 normalized16 rows16 checked16
  · exact extensions_of_normalized 17 free17 normalized17 rows17 checked17
  · exact extensions_of_normalized 18 free18 normalized18 rows18 checked18
  · exact extensions_of_normalized 19 free19 normalized19 rows19 checked19
  · exact extensions_of_normalized 20 free20 normalized20 rows20 checked20
  · exact extensions_of_normalized 21 free21 normalized21 rows21 checked21
  · exact extensions_of_normalized 22 free22 normalized22 rows22 checked22
  · exact extensions_of_normalized 23 free23 normalized23 rows23 checked23
  · exact extensions_of_normalized 24 free24 normalized24 rows24 checked24
  · exact extensions_of_normalized 25 free25 normalized25 rows25 checked25
  · exact extensions_of_normalized 26 free26 normalized26 rows26 checked26
  · exact extensions_of_normalized 27 free27 normalized27 rows27 checked27
  · exact extensions_of_normalized 28 free28 normalized28 rows28 checked28
  · exact extensions_of_normalized 29 free29 normalized29 rows29 checked29
  · exact extensions_of_normalized 30 free30 normalized30 rows30 checked30
  · exact extensions_of_normalized 31 free31 normalized31 rows31 checked31

end QiushiMatmul.GlobalOrbit.Cases1
