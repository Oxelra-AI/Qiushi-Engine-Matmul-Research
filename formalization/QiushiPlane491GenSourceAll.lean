import QiushiPlane491GenSourceBlock0
import QiushiPlane491GenSourceBlock1
import QiushiPlane491GenSourceBlock2
import QiushiPlane491GenSourceBlock3
import QiushiPlane491GenSourceBlock4
import QiushiPlane491GenSourceBlock5
import QiushiPlane491GenSourceBlock6
import QiushiPlane491GenSourceBlock7
import QiushiPlane491GenSourceBlock8
import QiushiPlane491GenSourceBlock9
import QiushiPlane491GenSourceBlock10
import QiushiPlane491GenSourceBlock11
import QiushiPlane491GenSourceBlock12
import QiushiPlane491GenSourceBlock13
import QiushiPlane491GenSourceBlock14
import QiushiPlane491GenSourceBlock15
import QiushiPlane491GenSourceBlock16
import QiushiPlane491GenSourceBlock17
import QiushiPlane491GenSourceBlock18
import QiushiPlane491GenSourceBlock19
import QiushiPlane491GenSourceBlock20
import QiushiPlane491GenSourceBlock21
import QiushiPlane491GenSourceBlock22
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane491GenSourceAll : forall i, plane491GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 23) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane491GenSourceBlock0
  | ⟨1, _⟩ => exact plane491GenSourceBlock1
  | ⟨2, _⟩ => exact plane491GenSourceBlock2
  | ⟨3, _⟩ => exact plane491GenSourceBlock3
  | ⟨4, _⟩ => exact plane491GenSourceBlock4
  | ⟨5, _⟩ => exact plane491GenSourceBlock5
  | ⟨6, _⟩ => exact plane491GenSourceBlock6
  | ⟨7, _⟩ => exact plane491GenSourceBlock7
  | ⟨8, _⟩ => exact plane491GenSourceBlock8
  | ⟨9, _⟩ => exact plane491GenSourceBlock9
  | ⟨10, _⟩ => exact plane491GenSourceBlock10
  | ⟨11, _⟩ => exact plane491GenSourceBlock11
  | ⟨12, _⟩ => exact plane491GenSourceBlock12
  | ⟨13, _⟩ => exact plane491GenSourceBlock13
  | ⟨14, _⟩ => exact plane491GenSourceBlock14
  | ⟨15, _⟩ => exact plane491GenSourceBlock15
  | ⟨16, _⟩ => exact plane491GenSourceBlock16
  | ⟨17, _⟩ => exact plane491GenSourceBlock17
  | ⟨18, _⟩ => exact plane491GenSourceBlock18
  | ⟨19, _⟩ => exact plane491GenSourceBlock19
  | ⟨20, _⟩ => exact plane491GenSourceBlock20
  | ⟨21, _⟩ => exact plane491GenSourceBlock21
  | ⟨22, _⟩ => exact plane491GenSourceBlock22
  | ⟨k + 23, h⟩ => omega
end QiushiMatmul
