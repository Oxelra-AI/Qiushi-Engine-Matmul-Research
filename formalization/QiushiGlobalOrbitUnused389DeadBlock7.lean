import QiushiGlobalOrbitUnused389CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane389UnusedGenDeadBlock7 : forall offset : Fin 32,
    forall hlt : 7 * 32 + offset.val < 512,
    plane389UnusedGenDeadProperty (Fin.mk (7 * 32 + offset.val) hlt) := by
  simp only [plane389UnusedGenDeadProperty, plane389UnusedGenConfig, plane389UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
