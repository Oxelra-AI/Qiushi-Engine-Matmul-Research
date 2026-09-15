import QiushiPlane454GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane454GenDeadBlock10 : forall offset : Fin 32,
    forall hlt : 10 * 32 + offset.val < 512,
    plane454GenDeadProperty (Fin.mk (10 * 32 + offset.val) hlt) := by
  simp only [plane454GenDeadProperty, plane454GenConfig, plane454GenOccSys]
  decide +kernel
end QiushiMatmul
