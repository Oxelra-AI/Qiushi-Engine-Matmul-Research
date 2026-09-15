import QiushiPlane466GenIndicatorBlock0
import QiushiPlane466GenIndicatorBlock1
import QiushiPlane466GenIndicatorBlock2
import QiushiPlane466GenIndicatorBlock3
import QiushiPlane466GenIndicatorBlock4
import QiushiPlane466GenIndicatorBlock5
import QiushiPlane466GenIndicatorBlock6
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane466GenIndicatorAll : forall i, plane466GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 7) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane466GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane466GenIndicatorBlock1
  | ⟨2, _⟩ => exact plane466GenIndicatorBlock2
  | ⟨3, _⟩ => exact plane466GenIndicatorBlock3
  | ⟨4, _⟩ => exact plane466GenIndicatorBlock4
  | ⟨5, _⟩ => exact plane466GenIndicatorBlock5
  | ⟨6, _⟩ => exact plane466GenIndicatorBlock6
  | ⟨k + 7, h⟩ => omega
end QiushiMatmul
