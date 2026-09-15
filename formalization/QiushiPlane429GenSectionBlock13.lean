import QiushiPlane429GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane429GenSectionBlock13 : forall offset : Fin 32,
    forall hlt : 13 * 32 + offset.val < 512,
    plane429GenSectionProperty (Fin.mk (13 * 32 + offset.val) hlt) := by
  simp only [plane429GenSectionProperty, plane429GenConfig, plane429GenOccSys]
  decide +kernel
end QiushiMatmul
