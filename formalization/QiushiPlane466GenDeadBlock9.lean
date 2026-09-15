import QiushiPlane466GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane466GenDeadBlock9 : forall offset : Fin 32,
    forall hlt : 9 * 32 + offset.val < 512,
    plane466GenDeadProperty (Fin.mk (9 * 32 + offset.val) hlt) := by
  simp only [plane466GenDeadProperty, plane466GenConfig, plane466GenOccSys]
  decide +kernel
end QiushiMatmul
