import QiushiPlane483GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane483GenDeadSourceBlock2 : forall offset : Fin 32,
    forall hlt : 2 * 32 + offset.val < 76,
    plane483GenDeadSourceProperty (Fin.mk (2 * 32 + offset.val) hlt) := by
  simp only [plane483GenDeadSourceProperty, plane483GenConfig, plane483GenOccSys]
  decide +kernel
end QiushiMatmul
