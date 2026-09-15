import QiushiPlane491GenIndicatorBlock0
import QiushiPlane491GenIndicatorBlock1
import QiushiPlane491GenIndicatorBlock2
import QiushiPlane491GenIndicatorBlock3
import QiushiPlane491GenIndicatorBlock4
import QiushiPlane491GenIndicatorBlock5
import QiushiPlane491GenIndicatorBlock6
import QiushiPlane491GenIndicatorBlock7
import QiushiPlane491GenIndicatorBlock8
import QiushiPlane491GenIndicatorBlock9
import QiushiPlane491GenIndicatorBlock10
import QiushiPlane491GenIndicatorBlock11
import QiushiPlane491GenIndicatorBlock12
import QiushiPlane491GenIndicatorBlock13
import QiushiPlane491GenIndicatorBlock14
import QiushiPlane491GenIndicatorBlock15
import QiushiPlane491GenIndicatorBlock16
import QiushiPlane491GenIndicatorBlock17
import QiushiPlane491GenIndicatorBlock18
import QiushiPlane491GenIndicatorBlock19
import QiushiPlane491GenIndicatorBlock20
import QiushiPlane491GenIndicatorBlock21
import QiushiPlane491GenIndicatorBlock22
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane491GenIndicatorAll : forall i, plane491GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 23) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane491GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane491GenIndicatorBlock1
  | ⟨2, _⟩ => exact plane491GenIndicatorBlock2
  | ⟨3, _⟩ => exact plane491GenIndicatorBlock3
  | ⟨4, _⟩ => exact plane491GenIndicatorBlock4
  | ⟨5, _⟩ => exact plane491GenIndicatorBlock5
  | ⟨6, _⟩ => exact plane491GenIndicatorBlock6
  | ⟨7, _⟩ => exact plane491GenIndicatorBlock7
  | ⟨8, _⟩ => exact plane491GenIndicatorBlock8
  | ⟨9, _⟩ => exact plane491GenIndicatorBlock9
  | ⟨10, _⟩ => exact plane491GenIndicatorBlock10
  | ⟨11, _⟩ => exact plane491GenIndicatorBlock11
  | ⟨12, _⟩ => exact plane491GenIndicatorBlock12
  | ⟨13, _⟩ => exact plane491GenIndicatorBlock13
  | ⟨14, _⟩ => exact plane491GenIndicatorBlock14
  | ⟨15, _⟩ => exact plane491GenIndicatorBlock15
  | ⟨16, _⟩ => exact plane491GenIndicatorBlock16
  | ⟨17, _⟩ => exact plane491GenIndicatorBlock17
  | ⟨18, _⟩ => exact plane491GenIndicatorBlock18
  | ⟨19, _⟩ => exact plane491GenIndicatorBlock19
  | ⟨20, _⟩ => exact plane491GenIndicatorBlock20
  | ⟨21, _⟩ => exact plane491GenIndicatorBlock21
  | ⟨22, _⟩ => exact plane491GenIndicatorBlock22
  | ⟨k + 23, h⟩ => omega
end QiushiMatmul
