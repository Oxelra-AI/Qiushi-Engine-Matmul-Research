import QiushiPlane448GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane448GenDeadBlock13 : forall offset : Fin 32,
    forall hlt : 13 * 32 + offset.val < 512,
    plane448GenDeadProperty (Fin.mk (13 * 32 + offset.val) hlt) := by
  simp only [plane448GenDeadProperty, plane448GenConfig, plane448GenOccSys]
  decide +kernel
end QiushiMatmul
