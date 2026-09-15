import QiushiPlane470GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane470GenSourceBlock3 : forall offset : Fin 32,
    forall hlt : 3 * 32 + offset.val < 232,
    plane470GenSourceProperty (Fin.mk (3 * 32 + offset.val) hlt) := by
  simp only [plane470GenSourceProperty, plane470GenConfig, plane470GenOccSys]
  decide +kernel
end QiushiMatmul
