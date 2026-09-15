import QiushiGlobalOrbitUnused302CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane302UnusedGenDeadBlock4 : forall offset : Fin 32,
    forall hlt : 4 * 32 + offset.val < 512,
    plane302UnusedGenDeadProperty (Fin.mk (4 * 32 + offset.val) hlt) := by
  simp only [plane302UnusedGenDeadProperty, plane302UnusedGenConfig, plane302UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
