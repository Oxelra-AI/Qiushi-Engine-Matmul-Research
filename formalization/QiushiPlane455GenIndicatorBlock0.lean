import QiushiPlane455GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane455GenIndicatorBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 124,
    plane455GenIndicatorProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane455GenIndicatorProperty, plane455GenConfig, plane455GenOccSys]
  decide +kernel
end QiushiMatmul
