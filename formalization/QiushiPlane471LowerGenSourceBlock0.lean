import QiushiPlane471LowerGenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane471LowerGenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 53,
    plane471LowerGenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane471LowerGenSourceProperty, plane471LowerGenConfig, plane471LowerGenOccSys]
  decide +kernel
end QiushiMatmul
