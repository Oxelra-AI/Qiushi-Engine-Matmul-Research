import QiushiPlane456LowerGenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane456LowerGenDeadBlock15 : forall offset : Fin 32,
    forall hlt : 15 * 32 + offset.val < 512,
    plane456LowerGenDeadProperty (Fin.mk (15 * 32 + offset.val) hlt) := by
  simp only [plane456LowerGenDeadProperty, plane456LowerGenConfig, plane456LowerGenOccSys]
  decide +kernel
end QiushiMatmul
