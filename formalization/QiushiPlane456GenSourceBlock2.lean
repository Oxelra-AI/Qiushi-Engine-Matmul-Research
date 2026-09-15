import QiushiPlane456GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane456GenSourceBlock2 : forall offset : Fin 32,
    forall hlt : 2 * 32 + offset.val < 248,
    plane456GenSourceProperty (Fin.mk (2 * 32 + offset.val) hlt) := by
  simp only [plane456GenSourceProperty, plane456GenConfig, plane456GenOccSys]
  decide +kernel
end QiushiMatmul
