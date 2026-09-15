import QiushiPlane481GenIndicatorBlock0
import QiushiPlane481GenIndicatorBlock1
import QiushiPlane481GenIndicatorBlock2
import QiushiPlane481GenIndicatorBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane481GenIndicatorAll : forall i, plane481GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane481GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane481GenIndicatorBlock1
  | ⟨2, _⟩ => exact plane481GenIndicatorBlock2
  | ⟨3, _⟩ => exact plane481GenIndicatorBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
