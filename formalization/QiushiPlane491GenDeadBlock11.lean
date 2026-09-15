import QiushiPlane491GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane491GenDeadBlock11 : forall offset : Fin 32,
    forall hlt : 11 * 32 + offset.val < 512,
    plane491GenDeadProperty (Fin.mk (11 * 32 + offset.val) hlt) := by
  simp only [plane491GenDeadProperty, plane491GenConfig, plane491GenOccSys]
  decide +kernel
end QiushiMatmul
