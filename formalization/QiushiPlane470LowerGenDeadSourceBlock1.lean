import QiushiPlane470LowerGenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane470LowerGenDeadSourceBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 50,
    plane470LowerGenDeadSourceProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane470LowerGenDeadSourceProperty, plane470LowerGenConfig, plane470LowerGenOccSys]
  decide +kernel
end QiushiMatmul
