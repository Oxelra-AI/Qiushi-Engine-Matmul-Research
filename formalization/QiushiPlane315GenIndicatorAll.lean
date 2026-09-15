import QiushiPlane315GenIndicatorBlock0
import QiushiPlane315GenIndicatorBlock1
import QiushiPlane315GenIndicatorBlock2
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane315GenIndicatorAll : forall i, plane315GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 3) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane315GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane315GenIndicatorBlock1
  | ⟨2, _⟩ => exact plane315GenIndicatorBlock2
  | ⟨k + 3, h⟩ => omega
end QiushiMatmul
