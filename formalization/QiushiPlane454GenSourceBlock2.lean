import QiushiPlane454GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane454GenSourceBlock2 : forall offset : Fin 32,
    forall hlt : 2 * 32 + offset.val < 174,
    plane454GenSourceProperty (Fin.mk (2 * 32 + offset.val) hlt) := by
  simp only [plane454GenSourceProperty, plane454GenConfig, plane454GenOccSys]
  decide +kernel
end QiushiMatmul
