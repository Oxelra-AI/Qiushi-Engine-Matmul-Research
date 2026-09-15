import QiushiPlane463LowerGenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane463LowerGenSectionBlock9 : forall offset : Fin 32,
    forall hlt : 9 * 32 + offset.val < 512,
    plane463LowerGenSectionProperty (Fin.mk (9 * 32 + offset.val) hlt) := by
  simp only [plane463LowerGenSectionProperty, plane463LowerGenConfig, plane463LowerGenOccSys]
  decide +kernel
end QiushiMatmul
