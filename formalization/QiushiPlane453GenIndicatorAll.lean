import QiushiPlane453GenIndicatorBlock0
import QiushiPlane453GenIndicatorBlock1
import QiushiPlane453GenIndicatorBlock2
import QiushiPlane453GenIndicatorBlock3
import QiushiPlane453GenIndicatorBlock4
import QiushiPlane453GenIndicatorBlock5
import QiushiPlane453GenIndicatorBlock6
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane453GenIndicatorAll : forall i, plane453GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 7) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane453GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane453GenIndicatorBlock1
  | ⟨2, _⟩ => exact plane453GenIndicatorBlock2
  | ⟨3, _⟩ => exact plane453GenIndicatorBlock3
  | ⟨4, _⟩ => exact plane453GenIndicatorBlock4
  | ⟨5, _⟩ => exact plane453GenIndicatorBlock5
  | ⟨6, _⟩ => exact plane453GenIndicatorBlock6
  | ⟨k + 7, h⟩ => omega
end QiushiMatmul
