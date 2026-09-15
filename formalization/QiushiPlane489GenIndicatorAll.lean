import QiushiPlane489GenIndicatorBlock0
import QiushiPlane489GenIndicatorBlock1
import QiushiPlane489GenIndicatorBlock2
import QiushiPlane489GenIndicatorBlock3
import QiushiPlane489GenIndicatorBlock4
import QiushiPlane489GenIndicatorBlock5
import QiushiPlane489GenIndicatorBlock6
import QiushiPlane489GenIndicatorBlock7
import QiushiPlane489GenIndicatorBlock8
import QiushiPlane489GenIndicatorBlock9
import QiushiPlane489GenIndicatorBlock10
import QiushiPlane489GenIndicatorBlock11
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane489GenIndicatorAll : forall i, plane489GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 12) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane489GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane489GenIndicatorBlock1
  | ⟨2, _⟩ => exact plane489GenIndicatorBlock2
  | ⟨3, _⟩ => exact plane489GenIndicatorBlock3
  | ⟨4, _⟩ => exact plane489GenIndicatorBlock4
  | ⟨5, _⟩ => exact plane489GenIndicatorBlock5
  | ⟨6, _⟩ => exact plane489GenIndicatorBlock6
  | ⟨7, _⟩ => exact plane489GenIndicatorBlock7
  | ⟨8, _⟩ => exact plane489GenIndicatorBlock8
  | ⟨9, _⟩ => exact plane489GenIndicatorBlock9
  | ⟨10, _⟩ => exact plane489GenIndicatorBlock10
  | ⟨11, _⟩ => exact plane489GenIndicatorBlock11
  | ⟨k + 12, h⟩ => omega
end QiushiMatmul
