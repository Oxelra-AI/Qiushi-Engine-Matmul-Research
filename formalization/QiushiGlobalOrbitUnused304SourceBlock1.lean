import QiushiGlobalOrbitUnused304CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane304UnusedGenSourceBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 35,
    plane304UnusedGenSourceProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane304UnusedGenSourceProperty, plane304UnusedGenConfig, plane304UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
