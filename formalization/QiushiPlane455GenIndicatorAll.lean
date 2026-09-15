import QiushiPlane455GenIndicatorBlock0
import QiushiPlane455GenIndicatorBlock1
import QiushiPlane455GenIndicatorBlock2
import QiushiPlane455GenIndicatorBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane455GenIndicatorAll : forall i, plane455GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane455GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane455GenIndicatorBlock1
  | ⟨2, _⟩ => exact plane455GenIndicatorBlock2
  | ⟨3, _⟩ => exact plane455GenIndicatorBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
