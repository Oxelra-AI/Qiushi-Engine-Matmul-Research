import QiushiPlane464GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane464GenDeadSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 13,
    plane464GenDeadSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane464GenDeadSourceProperty, plane464GenConfig, plane464GenOccSys]
  decide +kernel
end QiushiMatmul
