import QiushiPlane419GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane419GenDeadBlock15 : forall offset : Fin 32,
    forall hlt : 15 * 32 + offset.val < 512,
    plane419GenDeadProperty (Fin.mk (15 * 32 + offset.val) hlt) := by
  simp only [plane419GenDeadProperty, plane419GenConfig, plane419GenOccSys]
  decide +kernel
end QiushiMatmul
