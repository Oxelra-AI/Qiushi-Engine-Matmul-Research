import QiushiPlane490GenIndicatorBlock0
import QiushiPlane490GenIndicatorBlock1
import QiushiPlane490GenIndicatorBlock2
import QiushiPlane490GenIndicatorBlock3
import QiushiPlane490GenIndicatorBlock4
import QiushiPlane490GenIndicatorBlock5
import QiushiPlane490GenIndicatorBlock6
import QiushiPlane490GenIndicatorBlock7
import QiushiPlane490GenIndicatorBlock8
import QiushiPlane490GenIndicatorBlock9
import QiushiPlane490GenIndicatorBlock10
import QiushiPlane490GenIndicatorBlock11
import QiushiPlane490GenIndicatorBlock12
import QiushiPlane490GenIndicatorBlock13
import QiushiPlane490GenIndicatorBlock14
import QiushiPlane490GenIndicatorBlock15
import QiushiPlane490GenIndicatorBlock16
import QiushiPlane490GenIndicatorBlock17
import QiushiPlane490GenIndicatorBlock18
import QiushiPlane490GenIndicatorBlock19
import QiushiPlane490GenIndicatorBlock20
import QiushiPlane490GenIndicatorBlock21
import QiushiPlane490GenIndicatorBlock22
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane490GenIndicatorAll : forall i, plane490GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 23) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane490GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane490GenIndicatorBlock1
  | ⟨2, _⟩ => exact plane490GenIndicatorBlock2
  | ⟨3, _⟩ => exact plane490GenIndicatorBlock3
  | ⟨4, _⟩ => exact plane490GenIndicatorBlock4
  | ⟨5, _⟩ => exact plane490GenIndicatorBlock5
  | ⟨6, _⟩ => exact plane490GenIndicatorBlock6
  | ⟨7, _⟩ => exact plane490GenIndicatorBlock7
  | ⟨8, _⟩ => exact plane490GenIndicatorBlock8
  | ⟨9, _⟩ => exact plane490GenIndicatorBlock9
  | ⟨10, _⟩ => exact plane490GenIndicatorBlock10
  | ⟨11, _⟩ => exact plane490GenIndicatorBlock11
  | ⟨12, _⟩ => exact plane490GenIndicatorBlock12
  | ⟨13, _⟩ => exact plane490GenIndicatorBlock13
  | ⟨14, _⟩ => exact plane490GenIndicatorBlock14
  | ⟨15, _⟩ => exact plane490GenIndicatorBlock15
  | ⟨16, _⟩ => exact plane490GenIndicatorBlock16
  | ⟨17, _⟩ => exact plane490GenIndicatorBlock17
  | ⟨18, _⟩ => exact plane490GenIndicatorBlock18
  | ⟨19, _⟩ => exact plane490GenIndicatorBlock19
  | ⟨20, _⟩ => exact plane490GenIndicatorBlock20
  | ⟨21, _⟩ => exact plane490GenIndicatorBlock21
  | ⟨22, _⟩ => exact plane490GenIndicatorBlock22
  | ⟨k + 23, h⟩ => omega
end QiushiMatmul
