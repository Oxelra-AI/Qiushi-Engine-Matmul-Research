import QiushiGlobalOrbitUnused248CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane248UnusedGenDeadBlock14 : forall offset : Fin 32,
    forall hlt : 14 * 32 + offset.val < 512,
    plane248UnusedGenDeadProperty (Fin.mk (14 * 32 + offset.val) hlt) := by
  simp only [plane248UnusedGenDeadProperty, plane248UnusedGenConfig, plane248UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
