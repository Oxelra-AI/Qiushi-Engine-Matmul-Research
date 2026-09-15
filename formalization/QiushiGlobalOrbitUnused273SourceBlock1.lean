import QiushiGlobalOrbitUnused273CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane273UnusedGenSourceBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 44,
    plane273UnusedGenSourceProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane273UnusedGenSourceProperty, plane273UnusedGenConfig, plane273UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
