import QiushiPlane471LowerGenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane471LowerGenSectionBlock13 : forall offset : Fin 32,
    forall hlt : 13 * 32 + offset.val < 512,
    plane471LowerGenSectionProperty (Fin.mk (13 * 32 + offset.val) hlt) := by
  simp only [plane471LowerGenSectionProperty, plane471LowerGenConfig, plane471LowerGenOccSys]
  decide +kernel
end QiushiMatmul
