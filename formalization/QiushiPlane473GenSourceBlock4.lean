import QiushiPlane473GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane473GenSourceBlock4 : forall offset : Fin 32,
    forall hlt : 4 * 32 + offset.val < 153,
    plane473GenSourceProperty (Fin.mk (4 * 32 + offset.val) hlt) := by
  simp only [plane473GenSourceProperty, plane473GenConfig, plane473GenOccSys]
  decide +kernel
end QiushiMatmul
