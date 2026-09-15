import QiushiPlane468GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane468GenDeadBlock14 : forall offset : Fin 32,
    forall hlt : 14 * 32 + offset.val < 512,
    plane468GenDeadProperty (Fin.mk (14 * 32 + offset.val) hlt) := by
  simp only [plane468GenDeadProperty, plane468GenConfig, plane468GenOccSys]
  decide +kernel
end QiushiMatmul
