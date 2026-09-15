import QiushiGlobalOrbitUnused240CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane240UnusedGenDeadBlock13 : forall offset : Fin 32,
    forall hlt : 13 * 32 + offset.val < 512,
    plane240UnusedGenDeadProperty (Fin.mk (13 * 32 + offset.val) hlt) := by
  simp only [plane240UnusedGenDeadProperty, plane240UnusedGenConfig, plane240UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
