import QiushiPlane465GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane465GenSectionBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 512,
    plane465GenSectionProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane465GenSectionProperty, plane465GenConfig, plane465GenOccSys]
  decide +kernel
end QiushiMatmul
