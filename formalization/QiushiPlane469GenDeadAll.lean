import QiushiPlane469GenDeadBlock0
import QiushiPlane469GenDeadBlock1
import QiushiPlane469GenDeadBlock2
import QiushiPlane469GenDeadBlock3
import QiushiPlane469GenDeadBlock4
import QiushiPlane469GenDeadBlock5
import QiushiPlane469GenDeadBlock6
import QiushiPlane469GenDeadBlock7
import QiushiPlane469GenDeadBlock8
import QiushiPlane469GenDeadBlock9
import QiushiPlane469GenDeadBlock10
import QiushiPlane469GenDeadBlock11
import QiushiPlane469GenDeadBlock12
import QiushiPlane469GenDeadBlock13
import QiushiPlane469GenDeadBlock14
import QiushiPlane469GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane469GenDeadAll : forall i, plane469GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane469GenDeadBlock0
  | ⟨1, _⟩ => exact plane469GenDeadBlock1
  | ⟨2, _⟩ => exact plane469GenDeadBlock2
  | ⟨3, _⟩ => exact plane469GenDeadBlock3
  | ⟨4, _⟩ => exact plane469GenDeadBlock4
  | ⟨5, _⟩ => exact plane469GenDeadBlock5
  | ⟨6, _⟩ => exact plane469GenDeadBlock6
  | ⟨7, _⟩ => exact plane469GenDeadBlock7
  | ⟨8, _⟩ => exact plane469GenDeadBlock8
  | ⟨9, _⟩ => exact plane469GenDeadBlock9
  | ⟨10, _⟩ => exact plane469GenDeadBlock10
  | ⟨11, _⟩ => exact plane469GenDeadBlock11
  | ⟨12, _⟩ => exact plane469GenDeadBlock12
  | ⟨13, _⟩ => exact plane469GenDeadBlock13
  | ⟨14, _⟩ => exact plane469GenDeadBlock14
  | ⟨15, _⟩ => exact plane469GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
