import QiushiPlane434GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane434GenSourceBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 63,
    plane434GenSourceProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane434GenSourceProperty, plane434GenConfig, plane434GenOccSys]
  decide +kernel
end QiushiMatmul
