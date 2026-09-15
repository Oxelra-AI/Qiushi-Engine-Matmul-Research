import QiushiGlobalOrbitUnused307CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane307UnusedGenDeadBlock0 : forall offset : Fin 128,
    forall hlt : 0 * 128 + offset.val < 512,
    plane307UnusedGenDeadProperty (Fin.mk (0 * 128 + offset.val) hlt) := by
  simp only [plane307UnusedGenDeadProperty, plane307UnusedGenConfig, plane307UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
