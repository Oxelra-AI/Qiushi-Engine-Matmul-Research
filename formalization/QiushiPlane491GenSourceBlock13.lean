import QiushiPlane491GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane491GenSourceBlock13 : forall offset : Fin 32,
    forall hlt : 13 * 32 + offset.val < 726,
    plane491GenSourceProperty (Fin.mk (13 * 32 + offset.val) hlt) := by
  simp only [plane491GenSourceProperty, plane491GenConfig, plane491GenOccSys]
  decide +kernel
end QiushiMatmul
