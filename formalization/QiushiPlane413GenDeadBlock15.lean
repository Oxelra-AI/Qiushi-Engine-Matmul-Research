import QiushiPlane413GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane413GenDeadBlock15 : forall offset : Fin 32,
    forall hlt : 15 * 32 + offset.val < 512,
    plane413GenDeadProperty (Fin.mk (15 * 32 + offset.val) hlt) := by
  simp only [plane413GenDeadProperty, plane413GenConfig, plane413GenOccSys]
  decide +kernel
end QiushiMatmul
