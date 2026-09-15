import QiushiPlane470LowerGenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane470LowerGenSectionBlock8 : forall offset : Fin 32,
    forall hlt : 8 * 32 + offset.val < 512,
    plane470LowerGenSectionProperty (Fin.mk (8 * 32 + offset.val) hlt) := by
  simp only [plane470LowerGenSectionProperty, plane470LowerGenConfig, plane470LowerGenOccSys]
  decide +kernel
end QiushiMatmul
