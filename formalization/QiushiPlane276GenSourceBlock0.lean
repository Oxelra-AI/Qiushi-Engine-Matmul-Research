import QiushiPlane276GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane276GenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 37,
    plane276GenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane276GenSourceProperty, plane276GenConfig, plane276GenOccSys]
  decide +kernel
end QiushiMatmul
