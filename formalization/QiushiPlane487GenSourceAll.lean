import QiushiPlane487GenSourceBlock0
import QiushiPlane487GenSourceBlock1
import QiushiPlane487GenSourceBlock2
import QiushiPlane487GenSourceBlock3
import QiushiPlane487GenSourceBlock4
import QiushiPlane487GenSourceBlock5
import QiushiPlane487GenSourceBlock6
import QiushiPlane487GenSourceBlock7
import QiushiPlane487GenSourceBlock8
import QiushiPlane487GenSourceBlock9
import QiushiPlane487GenSourceBlock10
import QiushiPlane487GenSourceBlock11
import QiushiPlane487GenSourceBlock12
import QiushiPlane487GenSourceBlock13
import QiushiPlane487GenSourceBlock14
import QiushiPlane487GenSourceBlock15
import QiushiPlane487GenSourceBlock16
import QiushiPlane487GenSourceBlock17
import QiushiPlane487GenSourceBlock18
import QiushiPlane487GenSourceBlock19
import QiushiPlane487GenSourceBlock20
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane487GenSourceAll : forall i, plane487GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 21) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane487GenSourceBlock0
  | ⟨1, _⟩ => exact plane487GenSourceBlock1
  | ⟨2, _⟩ => exact plane487GenSourceBlock2
  | ⟨3, _⟩ => exact plane487GenSourceBlock3
  | ⟨4, _⟩ => exact plane487GenSourceBlock4
  | ⟨5, _⟩ => exact plane487GenSourceBlock5
  | ⟨6, _⟩ => exact plane487GenSourceBlock6
  | ⟨7, _⟩ => exact plane487GenSourceBlock7
  | ⟨8, _⟩ => exact plane487GenSourceBlock8
  | ⟨9, _⟩ => exact plane487GenSourceBlock9
  | ⟨10, _⟩ => exact plane487GenSourceBlock10
  | ⟨11, _⟩ => exact plane487GenSourceBlock11
  | ⟨12, _⟩ => exact plane487GenSourceBlock12
  | ⟨13, _⟩ => exact plane487GenSourceBlock13
  | ⟨14, _⟩ => exact plane487GenSourceBlock14
  | ⟨15, _⟩ => exact plane487GenSourceBlock15
  | ⟨16, _⟩ => exact plane487GenSourceBlock16
  | ⟨17, _⟩ => exact plane487GenSourceBlock17
  | ⟨18, _⟩ => exact plane487GenSourceBlock18
  | ⟨19, _⟩ => exact plane487GenSourceBlock19
  | ⟨20, _⟩ => exact plane487GenSourceBlock20
  | ⟨k + 21, h⟩ => omega
end QiushiMatmul
