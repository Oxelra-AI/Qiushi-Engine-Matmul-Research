import QiushiPlane461GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane461GenSourceBlock3 : forall offset : Fin 32,
    forall hlt : 3 * 32 + offset.val < 151,
    plane461GenSourceProperty (Fin.mk (3 * 32 + offset.val) hlt) := by
  simp only [plane461GenSourceProperty, plane461GenConfig, plane461GenOccSys]
  decide +kernel
end QiushiMatmul
