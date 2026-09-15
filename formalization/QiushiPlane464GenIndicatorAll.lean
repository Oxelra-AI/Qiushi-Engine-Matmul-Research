import QiushiPlane464GenIndicatorBlock0
import QiushiPlane464GenIndicatorBlock1
import QiushiPlane464GenIndicatorBlock2
import QiushiPlane464GenIndicatorBlock3
import QiushiPlane464GenIndicatorBlock4
import QiushiPlane464GenIndicatorBlock5
import QiushiPlane464GenIndicatorBlock6
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane464GenIndicatorAll : forall i, plane464GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 7) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane464GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane464GenIndicatorBlock1
  | ⟨2, _⟩ => exact plane464GenIndicatorBlock2
  | ⟨3, _⟩ => exact plane464GenIndicatorBlock3
  | ⟨4, _⟩ => exact plane464GenIndicatorBlock4
  | ⟨5, _⟩ => exact plane464GenIndicatorBlock5
  | ⟨6, _⟩ => exact plane464GenIndicatorBlock6
  | ⟨k + 7, h⟩ => omega
end QiushiMatmul
