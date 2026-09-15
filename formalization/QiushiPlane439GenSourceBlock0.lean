import QiushiPlane439GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane439GenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 59,
    plane439GenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane439GenSourceProperty, plane439GenConfig, plane439GenOccSys]
  decide +kernel
end QiushiMatmul
