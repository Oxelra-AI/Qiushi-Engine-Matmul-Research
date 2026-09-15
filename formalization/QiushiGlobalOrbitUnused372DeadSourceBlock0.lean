import QiushiGlobalOrbitUnused372CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane372UnusedGenDeadSourceBlock0 : forall offset : Fin 128,
    forall hlt : 0 * 128 + offset.val < 5,
    plane372UnusedGenDeadSourceProperty (Fin.mk (0 * 128 + offset.val) hlt) := by
  simp only [plane372UnusedGenDeadSourceProperty, plane372UnusedGenConfig, plane372UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
