import QiushiPlane468GenIndicatorBlock0
import QiushiPlane468GenIndicatorBlock1
import QiushiPlane468GenIndicatorBlock2
import QiushiPlane468GenIndicatorBlock3
import QiushiPlane468GenIndicatorBlock4
import QiushiPlane468GenIndicatorBlock5
import QiushiPlane468GenIndicatorBlock6
import QiushiPlane468GenIndicatorBlock7
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane468GenIndicatorAll : forall i, plane468GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 8) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane468GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane468GenIndicatorBlock1
  | ⟨2, _⟩ => exact plane468GenIndicatorBlock2
  | ⟨3, _⟩ => exact plane468GenIndicatorBlock3
  | ⟨4, _⟩ => exact plane468GenIndicatorBlock4
  | ⟨5, _⟩ => exact plane468GenIndicatorBlock5
  | ⟨6, _⟩ => exact plane468GenIndicatorBlock6
  | ⟨7, _⟩ => exact plane468GenIndicatorBlock7
  | ⟨k + 8, h⟩ => omega
end QiushiMatmul
