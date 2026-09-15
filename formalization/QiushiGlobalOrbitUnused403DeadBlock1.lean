import QiushiGlobalOrbitUnused403CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane403UnusedGenDeadBlock1 : forall offset : Fin 128,
    forall hlt : 1 * 128 + offset.val < 512,
    plane403UnusedGenDeadProperty (Fin.mk (1 * 128 + offset.val) hlt) := by
  simp only [plane403UnusedGenDeadProperty, plane403UnusedGenConfig, plane403UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
