import QiushiPlane481GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane481GenDeadBlock4 : forall offset : Fin 32,
    forall hlt : 4 * 32 + offset.val < 512,
    plane481GenDeadProperty (Fin.mk (4 * 32 + offset.val) hlt) := by
  simp only [plane481GenDeadProperty, plane481GenConfig, plane481GenOccSys]
  decide +kernel
end QiushiMatmul
