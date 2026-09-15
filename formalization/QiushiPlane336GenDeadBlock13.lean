import QiushiPlane336GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane336GenDeadBlock13 : forall offset : Fin 32,
    forall hlt : 13 * 32 + offset.val < 512,
    plane336GenDeadProperty (Fin.mk (13 * 32 + offset.val) hlt) := by
  simp only [plane336GenDeadProperty, plane336GenConfig, plane336GenOccSys]
  decide +kernel
end QiushiMatmul
