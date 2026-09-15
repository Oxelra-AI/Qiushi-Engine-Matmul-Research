import QiushiPlane482GenIndicatorBlock0
import QiushiPlane482GenIndicatorBlock1
import QiushiPlane482GenIndicatorBlock2
import QiushiPlane482GenIndicatorBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane482GenIndicatorAll : forall i, plane482GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane482GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane482GenIndicatorBlock1
  | ⟨2, _⟩ => exact plane482GenIndicatorBlock2
  | ⟨3, _⟩ => exact plane482GenIndicatorBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
