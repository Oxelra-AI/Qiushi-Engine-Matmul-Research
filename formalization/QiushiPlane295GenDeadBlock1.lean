import QiushiPlane295GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane295GenDeadBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 512,
    plane295GenDeadProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane295GenDeadProperty, plane295GenConfig, plane295GenOccSys]
  decide +kernel
end QiushiMatmul
