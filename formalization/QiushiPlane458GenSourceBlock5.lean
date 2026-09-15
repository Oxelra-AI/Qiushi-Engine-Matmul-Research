import QiushiPlane458GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane458GenSourceBlock5 : forall offset : Fin 32,
    forall hlt : 5 * 32 + offset.val < 203,
    plane458GenSourceProperty (Fin.mk (5 * 32 + offset.val) hlt) := by
  simp only [plane458GenSourceProperty, plane458GenConfig, plane458GenOccSys]
  decide +kernel
end QiushiMatmul
