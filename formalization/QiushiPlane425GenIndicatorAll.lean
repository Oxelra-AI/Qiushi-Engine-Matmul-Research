import QiushiPlane425GenIndicatorBlock0
import QiushiPlane425GenIndicatorBlock1
import QiushiPlane425GenIndicatorBlock2
import QiushiPlane425GenIndicatorBlock3
import QiushiPlane425GenIndicatorBlock4
import QiushiPlane425GenIndicatorBlock5
import QiushiPlane425GenIndicatorBlock6
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane425GenIndicatorAll : forall i, plane425GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 7) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane425GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane425GenIndicatorBlock1
  | ⟨2, _⟩ => exact plane425GenIndicatorBlock2
  | ⟨3, _⟩ => exact plane425GenIndicatorBlock3
  | ⟨4, _⟩ => exact plane425GenIndicatorBlock4
  | ⟨5, _⟩ => exact plane425GenIndicatorBlock5
  | ⟨6, _⟩ => exact plane425GenIndicatorBlock6
  | ⟨k + 7, h⟩ => omega
end QiushiMatmul
