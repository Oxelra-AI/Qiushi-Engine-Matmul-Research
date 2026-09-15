import QiushiPlane468GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane468GenSourceBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 253,
    plane468GenSourceProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane468GenSourceProperty, plane468GenConfig, plane468GenOccSys]
  decide +kernel
end QiushiMatmul
