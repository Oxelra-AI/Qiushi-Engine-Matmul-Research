import QiushiPlane457GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane457GenSourceBlock5 : forall offset : Fin 32,
    forall hlt : 5 * 32 + offset.val < 178,
    plane457GenSourceProperty (Fin.mk (5 * 32 + offset.val) hlt) := by
  simp only [plane457GenSourceProperty, plane457GenConfig, plane457GenOccSys]
  decide +kernel
end QiushiMatmul
