import QiushiGlobalOrbitUnused273CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane273UnusedGenDeadBlock10 : forall offset : Fin 32,
    forall hlt : 10 * 32 + offset.val < 512,
    plane273UnusedGenDeadProperty (Fin.mk (10 * 32 + offset.val) hlt) := by
  simp only [plane273UnusedGenDeadProperty, plane273UnusedGenConfig, plane273UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
