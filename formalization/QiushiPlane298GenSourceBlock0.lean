import QiushiPlane298GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane298GenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 28,
    plane298GenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane298GenSourceProperty, plane298GenConfig, plane298GenOccSys]
  decide +kernel
end QiushiMatmul
