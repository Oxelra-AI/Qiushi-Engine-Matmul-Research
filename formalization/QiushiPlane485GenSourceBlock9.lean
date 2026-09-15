import QiushiPlane485GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane485GenSourceBlock9 : forall offset : Fin 32,
    forall hlt : 9 * 32 + offset.val < 421,
    plane485GenSourceProperty (Fin.mk (9 * 32 + offset.val) hlt) := by
  simp only [plane485GenSourceProperty, plane485GenConfig, plane485GenOccSys]
  decide +kernel
end QiushiMatmul
