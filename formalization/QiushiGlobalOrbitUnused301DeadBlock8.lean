import QiushiGlobalOrbitUnused301CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane301UnusedGenDeadBlock8 : forall offset : Fin 32,
    forall hlt : 8 * 32 + offset.val < 512,
    plane301UnusedGenDeadProperty (Fin.mk (8 * 32 + offset.val) hlt) := by
  simp only [plane301UnusedGenDeadProperty, plane301UnusedGenConfig, plane301UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
