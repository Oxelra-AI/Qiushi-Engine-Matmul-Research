import QiushiGlobalOrbitUnused304CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane304UnusedGenDeadSourceBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 34,
    plane304UnusedGenDeadSourceProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane304UnusedGenDeadSourceProperty, plane304UnusedGenConfig, plane304UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
