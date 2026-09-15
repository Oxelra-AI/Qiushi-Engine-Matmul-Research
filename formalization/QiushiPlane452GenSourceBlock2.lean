import QiushiPlane452GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane452GenSourceBlock2 : forall offset : Fin 32,
    forall hlt : 2 * 32 + offset.val < 117,
    plane452GenSourceProperty (Fin.mk (2 * 32 + offset.val) hlt) := by
  simp only [plane452GenSourceProperty, plane452GenConfig, plane452GenOccSys]
  decide +kernel
end QiushiMatmul
