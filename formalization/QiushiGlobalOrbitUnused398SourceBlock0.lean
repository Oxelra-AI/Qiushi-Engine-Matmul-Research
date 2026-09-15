import QiushiGlobalOrbitUnused398CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane398UnusedGenSourceBlock0 : forall offset : Fin 128,
    forall hlt : 0 * 128 + offset.val < 25,
    plane398UnusedGenSourceProperty (Fin.mk (0 * 128 + offset.val) hlt) := by
  simp only [plane398UnusedGenSourceProperty, plane398UnusedGenConfig, plane398UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
