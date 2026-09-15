import QiushiGlobalOrbitUnused273CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane273UnusedGenDeadSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 43,
    plane273UnusedGenDeadSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane273UnusedGenDeadSourceProperty, plane273UnusedGenConfig, plane273UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
