import QiushiPlane488GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane488GenSectionBlock6 : forall offset : Fin 32,
    forall hlt : 6 * 32 + offset.val < 512,
    plane488GenSectionProperty (Fin.mk (6 * 32 + offset.val) hlt) := by
  simp only [plane488GenSectionProperty, plane488GenConfig, plane488GenOccSys]
  decide +kernel
end QiushiMatmul
