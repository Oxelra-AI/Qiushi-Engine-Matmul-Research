import QiushiGlobalOrbitUnused304CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane304UnusedGenDeadBlock11 : forall offset : Fin 32,
    forall hlt : 11 * 32 + offset.val < 512,
    plane304UnusedGenDeadProperty (Fin.mk (11 * 32 + offset.val) hlt) := by
  simp only [plane304UnusedGenDeadProperty, plane304UnusedGenConfig, plane304UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
