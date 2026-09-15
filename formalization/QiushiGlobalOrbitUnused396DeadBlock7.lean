import QiushiGlobalOrbitUnused396CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane396UnusedGenDeadBlock7 : forall offset : Fin 32,
    forall hlt : 7 * 32 + offset.val < 512,
    plane396UnusedGenDeadProperty (Fin.mk (7 * 32 + offset.val) hlt) := by
  simp only [plane396UnusedGenDeadProperty, plane396UnusedGenConfig, plane396UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
