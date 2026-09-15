import QiushiPlane269GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane269GenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 30,
    plane269GenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane269GenSourceProperty, plane269GenConfig, plane269GenOccSys]
  decide +kernel
end QiushiMatmul
