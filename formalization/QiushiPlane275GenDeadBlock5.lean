import QiushiPlane275GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane275GenDeadBlock5 : forall offset : Fin 32,
    forall hlt : 5 * 32 + offset.val < 512,
    plane275GenDeadProperty (Fin.mk (5 * 32 + offset.val) hlt) := by
  simp only [plane275GenDeadProperty, plane275GenConfig, plane275GenOccSys]
  decide +kernel
end QiushiMatmul
