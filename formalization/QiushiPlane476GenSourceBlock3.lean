import QiushiPlane476GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane476GenSourceBlock3 : forall offset : Fin 32,
    forall hlt : 3 * 32 + offset.val < 113,
    plane476GenSourceProperty (Fin.mk (3 * 32 + offset.val) hlt) := by
  simp only [plane476GenSourceProperty, plane476GenConfig, plane476GenOccSys]
  decide +kernel
end QiushiMatmul
