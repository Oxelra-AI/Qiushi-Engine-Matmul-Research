import QiushiGlobalOrbitUnused337CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane337UnusedGenDeadBlock6 : forall offset : Fin 32,
    forall hlt : 6 * 32 + offset.val < 512,
    plane337UnusedGenDeadProperty (Fin.mk (6 * 32 + offset.val) hlt) := by
  simp only [plane337UnusedGenDeadProperty, plane337UnusedGenConfig, plane337UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
