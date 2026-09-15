import QiushiPlane474GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane474GenSourceBlock4 : forall offset : Fin 32,
    forall hlt : 4 * 32 + offset.val < 146,
    plane474GenSourceProperty (Fin.mk (4 * 32 + offset.val) hlt) := by
  simp only [plane474GenSourceProperty, plane474GenConfig, plane474GenOccSys]
  decide +kernel
end QiushiMatmul
