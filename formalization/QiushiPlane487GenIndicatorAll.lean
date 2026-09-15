import QiushiPlane487GenIndicatorBlock0
import QiushiPlane487GenIndicatorBlock1
import QiushiPlane487GenIndicatorBlock2
import QiushiPlane487GenIndicatorBlock3
import QiushiPlane487GenIndicatorBlock4
import QiushiPlane487GenIndicatorBlock5
import QiushiPlane487GenIndicatorBlock6
import QiushiPlane487GenIndicatorBlock7
import QiushiPlane487GenIndicatorBlock8
import QiushiPlane487GenIndicatorBlock9
import QiushiPlane487GenIndicatorBlock10
import QiushiPlane487GenIndicatorBlock11
import QiushiPlane487GenIndicatorBlock12
import QiushiPlane487GenIndicatorBlock13
import QiushiPlane487GenIndicatorBlock14
import QiushiPlane487GenIndicatorBlock15
import QiushiPlane487GenIndicatorBlock16
import QiushiPlane487GenIndicatorBlock17
import QiushiPlane487GenIndicatorBlock18
import QiushiPlane487GenIndicatorBlock19
import QiushiPlane487GenIndicatorBlock20
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane487GenIndicatorAll : forall i, plane487GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 21) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane487GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane487GenIndicatorBlock1
  | ⟨2, _⟩ => exact plane487GenIndicatorBlock2
  | ⟨3, _⟩ => exact plane487GenIndicatorBlock3
  | ⟨4, _⟩ => exact plane487GenIndicatorBlock4
  | ⟨5, _⟩ => exact plane487GenIndicatorBlock5
  | ⟨6, _⟩ => exact plane487GenIndicatorBlock6
  | ⟨7, _⟩ => exact plane487GenIndicatorBlock7
  | ⟨8, _⟩ => exact plane487GenIndicatorBlock8
  | ⟨9, _⟩ => exact plane487GenIndicatorBlock9
  | ⟨10, _⟩ => exact plane487GenIndicatorBlock10
  | ⟨11, _⟩ => exact plane487GenIndicatorBlock11
  | ⟨12, _⟩ => exact plane487GenIndicatorBlock12
  | ⟨13, _⟩ => exact plane487GenIndicatorBlock13
  | ⟨14, _⟩ => exact plane487GenIndicatorBlock14
  | ⟨15, _⟩ => exact plane487GenIndicatorBlock15
  | ⟨16, _⟩ => exact plane487GenIndicatorBlock16
  | ⟨17, _⟩ => exact plane487GenIndicatorBlock17
  | ⟨18, _⟩ => exact plane487GenIndicatorBlock18
  | ⟨19, _⟩ => exact plane487GenIndicatorBlock19
  | ⟨20, _⟩ => exact plane487GenIndicatorBlock20
  | ⟨k + 21, h⟩ => omega
end QiushiMatmul
