import QiushiGlobalOrbitUnused379CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane379UnusedGenDeadSourceBlock0 : forall offset : Fin 128,
    forall hlt : 0 * 128 + offset.val < 15,
    plane379UnusedGenDeadSourceProperty (Fin.mk (0 * 128 + offset.val) hlt) := by
  simp only [plane379UnusedGenDeadSourceProperty, plane379UnusedGenConfig, plane379UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
