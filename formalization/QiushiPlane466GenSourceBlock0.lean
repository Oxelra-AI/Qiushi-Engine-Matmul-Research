import QiushiPlane466GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane466GenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 210,
    plane466GenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane466GenSourceProperty, plane466GenConfig, plane466GenOccSys]
  decide +kernel
end QiushiMatmul
