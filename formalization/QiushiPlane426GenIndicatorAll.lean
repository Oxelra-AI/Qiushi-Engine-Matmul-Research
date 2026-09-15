import QiushiPlane426GenIndicatorBlock0
import QiushiPlane426GenIndicatorBlock1
import QiushiPlane426GenIndicatorBlock2
import QiushiPlane426GenIndicatorBlock3
import QiushiPlane426GenIndicatorBlock4
import QiushiPlane426GenIndicatorBlock5
import QiushiPlane426GenIndicatorBlock6
import QiushiPlane426GenIndicatorBlock7
import QiushiPlane426GenIndicatorBlock8
import QiushiPlane426GenIndicatorBlock9
import QiushiPlane426GenIndicatorBlock10
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane426GenIndicatorAll : forall i, plane426GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 11) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane426GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane426GenIndicatorBlock1
  | ⟨2, _⟩ => exact plane426GenIndicatorBlock2
  | ⟨3, _⟩ => exact plane426GenIndicatorBlock3
  | ⟨4, _⟩ => exact plane426GenIndicatorBlock4
  | ⟨5, _⟩ => exact plane426GenIndicatorBlock5
  | ⟨6, _⟩ => exact plane426GenIndicatorBlock6
  | ⟨7, _⟩ => exact plane426GenIndicatorBlock7
  | ⟨8, _⟩ => exact plane426GenIndicatorBlock8
  | ⟨9, _⟩ => exact plane426GenIndicatorBlock9
  | ⟨10, _⟩ => exact plane426GenIndicatorBlock10
  | ⟨k + 11, h⟩ => omega
end QiushiMatmul
