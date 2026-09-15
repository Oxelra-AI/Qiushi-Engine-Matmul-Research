import QiushiPlane274GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane274GenDeadBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 512,
    plane274GenDeadProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane274GenDeadProperty, plane274GenConfig, plane274GenOccSys]
  decide +kernel
end QiushiMatmul
