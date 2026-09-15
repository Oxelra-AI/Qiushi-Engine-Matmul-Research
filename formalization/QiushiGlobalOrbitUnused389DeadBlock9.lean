import QiushiGlobalOrbitUnused389CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane389UnusedGenDeadBlock9 : forall offset : Fin 32,
    forall hlt : 9 * 32 + offset.val < 512,
    plane389UnusedGenDeadProperty (Fin.mk (9 * 32 + offset.val) hlt) := by
  simp only [plane389UnusedGenDeadProperty, plane389UnusedGenConfig, plane389UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
