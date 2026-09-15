import QiushiPlane463GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane463GenDeadBlock12 : forall offset : Fin 32,
    forall hlt : 12 * 32 + offset.val < 512,
    plane463GenDeadProperty (Fin.mk (12 * 32 + offset.val) hlt) := by
  simp only [plane463GenDeadProperty, plane463GenConfig, plane463GenOccSys]
  decide +kernel
end QiushiMatmul
