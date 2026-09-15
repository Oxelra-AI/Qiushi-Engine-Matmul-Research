import QiushiPlane472GenDeadBlock0
import QiushiPlane472GenDeadBlock1
import QiushiPlane472GenDeadBlock2
import QiushiPlane472GenDeadBlock3
import QiushiPlane472GenDeadBlock4
import QiushiPlane472GenDeadBlock5
import QiushiPlane472GenDeadBlock6
import QiushiPlane472GenDeadBlock7
import QiushiPlane472GenDeadBlock8
import QiushiPlane472GenDeadBlock9
import QiushiPlane472GenDeadBlock10
import QiushiPlane472GenDeadBlock11
import QiushiPlane472GenDeadBlock12
import QiushiPlane472GenDeadBlock13
import QiushiPlane472GenDeadBlock14
import QiushiPlane472GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane472GenDeadAll : forall i, plane472GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane472GenDeadBlock0
  | ⟨1, _⟩ => exact plane472GenDeadBlock1
  | ⟨2, _⟩ => exact plane472GenDeadBlock2
  | ⟨3, _⟩ => exact plane472GenDeadBlock3
  | ⟨4, _⟩ => exact plane472GenDeadBlock4
  | ⟨5, _⟩ => exact plane472GenDeadBlock5
  | ⟨6, _⟩ => exact plane472GenDeadBlock6
  | ⟨7, _⟩ => exact plane472GenDeadBlock7
  | ⟨8, _⟩ => exact plane472GenDeadBlock8
  | ⟨9, _⟩ => exact plane472GenDeadBlock9
  | ⟨10, _⟩ => exact plane472GenDeadBlock10
  | ⟨11, _⟩ => exact plane472GenDeadBlock11
  | ⟨12, _⟩ => exact plane472GenDeadBlock12
  | ⟨13, _⟩ => exact plane472GenDeadBlock13
  | ⟨14, _⟩ => exact plane472GenDeadBlock14
  | ⟨15, _⟩ => exact plane472GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
