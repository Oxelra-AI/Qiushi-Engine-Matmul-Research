import QiushiGlobalOrbitUnused387CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane387UnusedGenDeadBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 512,
    plane387UnusedGenDeadProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane387UnusedGenDeadProperty, plane387UnusedGenConfig, plane387UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
