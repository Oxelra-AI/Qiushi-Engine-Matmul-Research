import QiushiPlane463LowerGenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane463LowerGenDeadSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 45,
    plane463LowerGenDeadSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane463LowerGenDeadSourceProperty, plane463LowerGenConfig, plane463LowerGenOccSys]
  decide +kernel
end QiushiMatmul
