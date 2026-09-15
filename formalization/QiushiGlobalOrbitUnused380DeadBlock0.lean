import QiushiGlobalOrbitUnused380CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane380UnusedGenDeadBlock0 : forall offset : Fin 128,
    forall hlt : 0 * 128 + offset.val < 512,
    plane380UnusedGenDeadProperty (Fin.mk (0 * 128 + offset.val) hlt) := by
  simp only [plane380UnusedGenDeadProperty, plane380UnusedGenConfig, plane380UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
