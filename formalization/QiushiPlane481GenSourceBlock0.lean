import QiushiPlane481GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane481GenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 116,
    plane481GenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane481GenSourceProperty, plane481GenConfig, plane481GenOccSys]
  decide +kernel
end QiushiMatmul
