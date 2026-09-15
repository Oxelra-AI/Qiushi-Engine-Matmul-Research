import QiushiGlobalOrbitUnused386CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane386UnusedGenDeadBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 512,
    plane386UnusedGenDeadProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane386UnusedGenDeadProperty, plane386UnusedGenConfig, plane386UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
