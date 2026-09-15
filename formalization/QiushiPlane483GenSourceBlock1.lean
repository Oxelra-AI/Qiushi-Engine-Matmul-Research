import QiushiPlane483GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane483GenSourceBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 112,
    plane483GenSourceProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane483GenSourceProperty, plane483GenConfig, plane483GenOccSys]
  decide +kernel
end QiushiMatmul
