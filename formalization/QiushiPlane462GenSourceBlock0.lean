import QiushiPlane462GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane462GenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 294,
    plane462GenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane462GenSourceProperty, plane462GenConfig, plane462GenOccSys]
  decide +kernel
end QiushiMatmul
