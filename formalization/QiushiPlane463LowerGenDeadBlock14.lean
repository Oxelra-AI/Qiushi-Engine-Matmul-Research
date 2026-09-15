import QiushiPlane463LowerGenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane463LowerGenDeadBlock14 : forall offset : Fin 32,
    forall hlt : 14 * 32 + offset.val < 512,
    plane463LowerGenDeadProperty (Fin.mk (14 * 32 + offset.val) hlt) := by
  simp only [plane463LowerGenDeadProperty, plane463LowerGenConfig, plane463LowerGenOccSys]
  decide +kernel
end QiushiMatmul
