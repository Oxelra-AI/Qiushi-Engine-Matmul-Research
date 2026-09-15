import QiushiPlane429GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane429GenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 55,
    plane429GenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane429GenSourceProperty, plane429GenConfig, plane429GenOccSys]
  decide +kernel
end QiushiMatmul
