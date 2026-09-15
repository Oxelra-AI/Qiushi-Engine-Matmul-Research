import QiushiGlobalOrbitUnused306CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane306UnusedGenDeadBlock1 : forall offset : Fin 128,
    forall hlt : 1 * 128 + offset.val < 512,
    plane306UnusedGenDeadProperty (Fin.mk (1 * 128 + offset.val) hlt) := by
  simp only [plane306UnusedGenDeadProperty, plane306UnusedGenConfig, plane306UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
