import QiushiPlane458GenIndicatorBlock0
import QiushiPlane458GenIndicatorBlock1
import QiushiPlane458GenIndicatorBlock2
import QiushiPlane458GenIndicatorBlock3
import QiushiPlane458GenIndicatorBlock4
import QiushiPlane458GenIndicatorBlock5
import QiushiPlane458GenIndicatorBlock6
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane458GenIndicatorAll : forall i, plane458GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 7) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane458GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane458GenIndicatorBlock1
  | ⟨2, _⟩ => exact plane458GenIndicatorBlock2
  | ⟨3, _⟩ => exact plane458GenIndicatorBlock3
  | ⟨4, _⟩ => exact plane458GenIndicatorBlock4
  | ⟨5, _⟩ => exact plane458GenIndicatorBlock5
  | ⟨6, _⟩ => exact plane458GenIndicatorBlock6
  | ⟨k + 7, h⟩ => omega
end QiushiMatmul
