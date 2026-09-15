import QiushiPlane485GenIndicatorBlock0
import QiushiPlane485GenIndicatorBlock1
import QiushiPlane485GenIndicatorBlock2
import QiushiPlane485GenIndicatorBlock3
import QiushiPlane485GenIndicatorBlock4
import QiushiPlane485GenIndicatorBlock5
import QiushiPlane485GenIndicatorBlock6
import QiushiPlane485GenIndicatorBlock7
import QiushiPlane485GenIndicatorBlock8
import QiushiPlane485GenIndicatorBlock9
import QiushiPlane485GenIndicatorBlock10
import QiushiPlane485GenIndicatorBlock11
import QiushiPlane485GenIndicatorBlock12
import QiushiPlane485GenIndicatorBlock13
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane485GenIndicatorAll : forall i, plane485GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 14) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane485GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane485GenIndicatorBlock1
  | ⟨2, _⟩ => exact plane485GenIndicatorBlock2
  | ⟨3, _⟩ => exact plane485GenIndicatorBlock3
  | ⟨4, _⟩ => exact plane485GenIndicatorBlock4
  | ⟨5, _⟩ => exact plane485GenIndicatorBlock5
  | ⟨6, _⟩ => exact plane485GenIndicatorBlock6
  | ⟨7, _⟩ => exact plane485GenIndicatorBlock7
  | ⟨8, _⟩ => exact plane485GenIndicatorBlock8
  | ⟨9, _⟩ => exact plane485GenIndicatorBlock9
  | ⟨10, _⟩ => exact plane485GenIndicatorBlock10
  | ⟨11, _⟩ => exact plane485GenIndicatorBlock11
  | ⟨12, _⟩ => exact plane485GenIndicatorBlock12
  | ⟨13, _⟩ => exact plane485GenIndicatorBlock13
  | ⟨k + 14, h⟩ => omega
end QiushiMatmul
