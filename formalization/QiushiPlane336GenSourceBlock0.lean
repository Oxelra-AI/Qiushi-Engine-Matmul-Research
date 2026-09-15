import QiushiPlane336GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane336GenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 34,
    plane336GenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane336GenSourceProperty, plane336GenConfig, plane336GenOccSys]
  decide +kernel
end QiushiMatmul
