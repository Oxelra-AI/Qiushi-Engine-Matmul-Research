import QiushiPlane456GenIndicatorBlock0
import QiushiPlane456GenIndicatorBlock1
import QiushiPlane456GenIndicatorBlock2
import QiushiPlane456GenIndicatorBlock3
import QiushiPlane456GenIndicatorBlock4
import QiushiPlane456GenIndicatorBlock5
import QiushiPlane456GenIndicatorBlock6
import QiushiPlane456GenIndicatorBlock7
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane456GenIndicatorAll : forall i, plane456GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 8) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane456GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane456GenIndicatorBlock1
  | ⟨2, _⟩ => exact plane456GenIndicatorBlock2
  | ⟨3, _⟩ => exact plane456GenIndicatorBlock3
  | ⟨4, _⟩ => exact plane456GenIndicatorBlock4
  | ⟨5, _⟩ => exact plane456GenIndicatorBlock5
  | ⟨6, _⟩ => exact plane456GenIndicatorBlock6
  | ⟨7, _⟩ => exact plane456GenIndicatorBlock7
  | ⟨k + 8, h⟩ => omega
end QiushiMatmul
