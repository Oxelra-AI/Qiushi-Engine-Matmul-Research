import QiushiPlane447GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane447GenDeadBlock11 : forall offset : Fin 32,
    forall hlt : 11 * 32 + offset.val < 512,
    plane447GenDeadProperty (Fin.mk (11 * 32 + offset.val) hlt) := by
  simp only [plane447GenDeadProperty, plane447GenConfig, plane447GenOccSys]
  decide +kernel
end QiushiMatmul
