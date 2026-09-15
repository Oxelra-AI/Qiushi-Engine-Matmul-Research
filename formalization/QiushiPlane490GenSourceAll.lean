import QiushiPlane490GenSourceBlock0
import QiushiPlane490GenSourceBlock1
import QiushiPlane490GenSourceBlock2
import QiushiPlane490GenSourceBlock3
import QiushiPlane490GenSourceBlock4
import QiushiPlane490GenSourceBlock5
import QiushiPlane490GenSourceBlock6
import QiushiPlane490GenSourceBlock7
import QiushiPlane490GenSourceBlock8
import QiushiPlane490GenSourceBlock9
import QiushiPlane490GenSourceBlock10
import QiushiPlane490GenSourceBlock11
import QiushiPlane490GenSourceBlock12
import QiushiPlane490GenSourceBlock13
import QiushiPlane490GenSourceBlock14
import QiushiPlane490GenSourceBlock15
import QiushiPlane490GenSourceBlock16
import QiushiPlane490GenSourceBlock17
import QiushiPlane490GenSourceBlock18
import QiushiPlane490GenSourceBlock19
import QiushiPlane490GenSourceBlock20
import QiushiPlane490GenSourceBlock21
import QiushiPlane490GenSourceBlock22
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane490GenSourceAll : forall i, plane490GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 23) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane490GenSourceBlock0
  | ⟨1, _⟩ => exact plane490GenSourceBlock1
  | ⟨2, _⟩ => exact plane490GenSourceBlock2
  | ⟨3, _⟩ => exact plane490GenSourceBlock3
  | ⟨4, _⟩ => exact plane490GenSourceBlock4
  | ⟨5, _⟩ => exact plane490GenSourceBlock5
  | ⟨6, _⟩ => exact plane490GenSourceBlock6
  | ⟨7, _⟩ => exact plane490GenSourceBlock7
  | ⟨8, _⟩ => exact plane490GenSourceBlock8
  | ⟨9, _⟩ => exact plane490GenSourceBlock9
  | ⟨10, _⟩ => exact plane490GenSourceBlock10
  | ⟨11, _⟩ => exact plane490GenSourceBlock11
  | ⟨12, _⟩ => exact plane490GenSourceBlock12
  | ⟨13, _⟩ => exact plane490GenSourceBlock13
  | ⟨14, _⟩ => exact plane490GenSourceBlock14
  | ⟨15, _⟩ => exact plane490GenSourceBlock15
  | ⟨16, _⟩ => exact plane490GenSourceBlock16
  | ⟨17, _⟩ => exact plane490GenSourceBlock17
  | ⟨18, _⟩ => exact plane490GenSourceBlock18
  | ⟨19, _⟩ => exact plane490GenSourceBlock19
  | ⟨20, _⟩ => exact plane490GenSourceBlock20
  | ⟨21, _⟩ => exact plane490GenSourceBlock21
  | ⟨22, _⟩ => exact plane490GenSourceBlock22
  | ⟨k + 23, h⟩ => omega
end QiushiMatmul
