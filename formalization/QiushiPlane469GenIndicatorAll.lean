import QiushiPlane469GenIndicatorBlock0
import QiushiPlane469GenIndicatorBlock1
import QiushiPlane469GenIndicatorBlock2
import QiushiPlane469GenIndicatorBlock3
import QiushiPlane469GenIndicatorBlock4
import QiushiPlane469GenIndicatorBlock5
import QiushiPlane469GenIndicatorBlock6
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane469GenIndicatorAll : forall i, plane469GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 7) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane469GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane469GenIndicatorBlock1
  | ⟨2, _⟩ => exact plane469GenIndicatorBlock2
  | ⟨3, _⟩ => exact plane469GenIndicatorBlock3
  | ⟨4, _⟩ => exact plane469GenIndicatorBlock4
  | ⟨5, _⟩ => exact plane469GenIndicatorBlock5
  | ⟨6, _⟩ => exact plane469GenIndicatorBlock6
  | ⟨k + 7, h⟩ => omega
end QiushiMatmul
