import QiushiPlane489GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane489GenSourceBlock11 : forall offset : Fin 32,
    forall hlt : 11 * 32 + offset.val < 371,
    plane489GenSourceProperty (Fin.mk (11 * 32 + offset.val) hlt) := by
  simp only [plane489GenSourceProperty, plane489GenConfig, plane489GenOccSys]
  decide +kernel
end QiushiMatmul
