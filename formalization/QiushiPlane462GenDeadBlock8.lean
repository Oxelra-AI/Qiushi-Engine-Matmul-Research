import QiushiPlane462GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane462GenDeadBlock8 : forall offset : Fin 32,
    forall hlt : 8 * 32 + offset.val < 512,
    plane462GenDeadProperty (Fin.mk (8 * 32 + offset.val) hlt) := by
  simp only [plane462GenDeadProperty, plane462GenConfig, plane462GenOccSys]
  decide +kernel
end QiushiMatmul
