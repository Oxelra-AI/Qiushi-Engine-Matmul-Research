import QiushiPlane474GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane474GenDeadBlock8 : forall offset : Fin 32,
    forall hlt : 8 * 32 + offset.val < 512,
    plane474GenDeadProperty (Fin.mk (8 * 32 + offset.val) hlt) := by
  simp only [plane474GenDeadProperty, plane474GenConfig, plane474GenOccSys]
  decide +kernel
end QiushiMatmul
