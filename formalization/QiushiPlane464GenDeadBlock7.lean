import QiushiPlane464GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane464GenDeadBlock7 : forall offset : Fin 32,
    forall hlt : 7 * 32 + offset.val < 512,
    plane464GenDeadProperty (Fin.mk (7 * 32 + offset.val) hlt) := by
  simp only [plane464GenDeadProperty, plane464GenConfig, plane464GenOccSys]
  decide +kernel
end QiushiMatmul
