import QiushiPlane452GenIndicatorBlock0
import QiushiPlane452GenIndicatorBlock1
import QiushiPlane452GenIndicatorBlock2
import QiushiPlane452GenIndicatorBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane452GenIndicatorAll : forall i, plane452GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane452GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane452GenIndicatorBlock1
  | ⟨2, _⟩ => exact plane452GenIndicatorBlock2
  | ⟨3, _⟩ => exact plane452GenIndicatorBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
