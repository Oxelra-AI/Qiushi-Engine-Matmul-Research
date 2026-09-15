import QiushiGlobalOrbitUnused328CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane328UnusedGenDeadBlock12 : forall offset : Fin 32,
    forall hlt : 12 * 32 + offset.val < 512,
    plane328UnusedGenDeadProperty (Fin.mk (12 * 32 + offset.val) hlt) := by
  simp only [plane328UnusedGenDeadProperty, plane328UnusedGenConfig, plane328UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
