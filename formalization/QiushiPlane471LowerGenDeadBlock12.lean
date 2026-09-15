import QiushiPlane471LowerGenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane471LowerGenDeadBlock12 : forall offset : Fin 32,
    forall hlt : 12 * 32 + offset.val < 512,
    plane471LowerGenDeadProperty (Fin.mk (12 * 32 + offset.val) hlt) := by
  simp only [plane471LowerGenDeadProperty, plane471LowerGenConfig, plane471LowerGenOccSys]
  decide +kernel
end QiushiMatmul
