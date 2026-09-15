import QiushiPlane255GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane255GenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 25,
    plane255GenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane255GenSourceProperty, plane255GenConfig, plane255GenOccSys]
  decide +kernel
end QiushiMatmul
