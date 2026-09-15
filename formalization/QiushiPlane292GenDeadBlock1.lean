import QiushiPlane292GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane292GenDeadBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 512,
    plane292GenDeadProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane292GenDeadProperty, plane292GenConfig, plane292GenOccSys]
  decide +kernel
end QiushiMatmul
