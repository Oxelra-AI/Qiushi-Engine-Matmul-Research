import QiushiCalibrationRowsTransport

namespace QiushiMatmul.CalibrationRows

/-- An explicit matrix-code basis for the image of any coded span. -/
theorem spanCodes_map_eq (bs : List Nat) (f : Mat3 →ₗ[F2] Mat3) :
    (spanCodes bs).map f = spanCodes (bs.map (fun c => matrixCodeNat (f (codeMat c)))) := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro M ⟨c, hc, rfl⟩
    change f (codeMat c) ∈ spanCodes _
    exact Submodule.subset_span ⟨_, List.mem_map.mpr ⟨c, hc, rfl⟩,
      (codeMat_matrixCode _).symm⟩
  · apply Submodule.span_le.mpr
    rintro M ⟨c, hc, rfl⟩
    obtain ⟨d, hd, he⟩ := List.mem_map.mp hc
    subst c
    rw [codeMat_matrixCode]
    exact ⟨codeMat d, Submodule.subset_span ⟨d, hd, rfl⟩, rfl⟩

end QiushiMatmul.CalibrationRows
