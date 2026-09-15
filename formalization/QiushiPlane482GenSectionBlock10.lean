import QiushiPlane482GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane482GenSectionBlock10 : forall offset : Fin 32,
    forall hlt : 10 * 32 + offset.val < 512,
    plane482GenSectionProperty (Fin.mk (10 * 32 + offset.val) hlt) := by
  simp only [plane482GenSectionProperty, plane482GenConfig, plane482GenOccSys]
  decide +kernel
end QiushiMatmul
