import QiushiPlane471GenIndicatorBlock0
import QiushiPlane471GenIndicatorBlock1
import QiushiPlane471GenIndicatorBlock2
import QiushiPlane471GenIndicatorBlock3
import QiushiPlane471GenIndicatorBlock4
import QiushiPlane471GenIndicatorBlock5
import QiushiPlane471GenIndicatorBlock6
import QiushiPlane471GenIndicatorBlock7
import QiushiPlane471GenIndicatorBlock8
import QiushiPlane471GenIndicatorBlock9
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane471GenIndicatorAll : forall i, plane471GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 10) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane471GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane471GenIndicatorBlock1
  | ⟨2, _⟩ => exact plane471GenIndicatorBlock2
  | ⟨3, _⟩ => exact plane471GenIndicatorBlock3
  | ⟨4, _⟩ => exact plane471GenIndicatorBlock4
  | ⟨5, _⟩ => exact plane471GenIndicatorBlock5
  | ⟨6, _⟩ => exact plane471GenIndicatorBlock6
  | ⟨7, _⟩ => exact plane471GenIndicatorBlock7
  | ⟨8, _⟩ => exact plane471GenIndicatorBlock8
  | ⟨9, _⟩ => exact plane471GenIndicatorBlock9
  | ⟨k + 10, h⟩ => omega
end QiushiMatmul
