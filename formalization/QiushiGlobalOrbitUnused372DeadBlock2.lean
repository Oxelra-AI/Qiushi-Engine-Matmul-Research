import QiushiGlobalOrbitUnused372CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane372UnusedGenDeadBlock2 : forall offset : Fin 128,
    forall hlt : 2 * 128 + offset.val < 512,
    plane372UnusedGenDeadProperty (Fin.mk (2 * 128 + offset.val) hlt) := by
  simp only [plane372UnusedGenDeadProperty, plane372UnusedGenConfig, plane372UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
