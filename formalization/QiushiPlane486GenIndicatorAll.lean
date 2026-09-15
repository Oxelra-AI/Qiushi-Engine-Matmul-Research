import QiushiPlane486GenIndicatorBlock0
import QiushiPlane486GenIndicatorBlock1
import QiushiPlane486GenIndicatorBlock2
import QiushiPlane486GenIndicatorBlock3
import QiushiPlane486GenIndicatorBlock4
import QiushiPlane486GenIndicatorBlock5
import QiushiPlane486GenIndicatorBlock6
import QiushiPlane486GenIndicatorBlock7
import QiushiPlane486GenIndicatorBlock8
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane486GenIndicatorAll : forall i, plane486GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 9) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane486GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane486GenIndicatorBlock1
  | ⟨2, _⟩ => exact plane486GenIndicatorBlock2
  | ⟨3, _⟩ => exact plane486GenIndicatorBlock3
  | ⟨4, _⟩ => exact plane486GenIndicatorBlock4
  | ⟨5, _⟩ => exact plane486GenIndicatorBlock5
  | ⟨6, _⟩ => exact plane486GenIndicatorBlock6
  | ⟨7, _⟩ => exact plane486GenIndicatorBlock7
  | ⟨8, _⟩ => exact plane486GenIndicatorBlock8
  | ⟨k + 9, h⟩ => omega
end QiushiMatmul
