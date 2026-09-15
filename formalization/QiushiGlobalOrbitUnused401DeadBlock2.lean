import QiushiGlobalOrbitUnused401CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane401UnusedGenDeadBlock2 : forall offset : Fin 128,
    forall hlt : 2 * 128 + offset.val < 512,
    plane401UnusedGenDeadProperty (Fin.mk (2 * 128 + offset.val) hlt) := by
  simp only [plane401UnusedGenDeadProperty, plane401UnusedGenConfig, plane401UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
