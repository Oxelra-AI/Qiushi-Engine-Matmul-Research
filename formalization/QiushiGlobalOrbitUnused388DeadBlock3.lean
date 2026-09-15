import QiushiGlobalOrbitUnused388CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane388UnusedGenDeadBlock3 : forall offset : Fin 32,
    forall hlt : 3 * 32 + offset.val < 512,
    plane388UnusedGenDeadProperty (Fin.mk (3 * 32 + offset.val) hlt) := by
  simp only [plane388UnusedGenDeadProperty, plane388UnusedGenConfig, plane388UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
