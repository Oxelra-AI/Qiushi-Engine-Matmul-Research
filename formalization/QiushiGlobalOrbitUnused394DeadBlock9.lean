import QiushiGlobalOrbitUnused394CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane394UnusedGenDeadBlock9 : forall offset : Fin 32,
    forall hlt : 9 * 32 + offset.val < 512,
    plane394UnusedGenDeadProperty (Fin.mk (9 * 32 + offset.val) hlt) := by
  simp only [plane394UnusedGenDeadProperty, plane394UnusedGenConfig, plane394UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
