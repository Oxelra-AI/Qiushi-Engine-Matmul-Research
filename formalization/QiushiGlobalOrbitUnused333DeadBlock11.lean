import QiushiGlobalOrbitUnused333CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane333UnusedGenDeadBlock11 : forall offset : Fin 32,
    forall hlt : 11 * 32 + offset.val < 512,
    plane333UnusedGenDeadProperty (Fin.mk (11 * 32 + offset.val) hlt) := by
  simp only [plane333UnusedGenDeadProperty, plane333UnusedGenConfig, plane333UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
