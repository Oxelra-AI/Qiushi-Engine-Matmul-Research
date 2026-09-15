import QiushiPlane295GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane295GenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 46,
    plane295GenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane295GenSourceProperty, plane295GenConfig, plane295GenOccSys]
  decide +kernel
end QiushiMatmul
