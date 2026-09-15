import QiushiGlobalOrbitUnused383CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane383UnusedGenDeadBlock3 : forall offset : Fin 128,
    forall hlt : 3 * 128 + offset.val < 512,
    plane383UnusedGenDeadProperty (Fin.mk (3 * 128 + offset.val) hlt) := by
  simp only [plane383UnusedGenDeadProperty, plane383UnusedGenConfig, plane383UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
