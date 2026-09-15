import QiushiPlane459GenDeadBlock0
import QiushiPlane459GenDeadBlock1
import QiushiPlane459GenDeadBlock2
import QiushiPlane459GenDeadBlock3
import QiushiPlane459GenDeadBlock4
import QiushiPlane459GenDeadBlock5
import QiushiPlane459GenDeadBlock6
import QiushiPlane459GenDeadBlock7
import QiushiPlane459GenDeadBlock8
import QiushiPlane459GenDeadBlock9
import QiushiPlane459GenDeadBlock10
import QiushiPlane459GenDeadBlock11
import QiushiPlane459GenDeadBlock12
import QiushiPlane459GenDeadBlock13
import QiushiPlane459GenDeadBlock14
import QiushiPlane459GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane459GenDeadAll : forall i, plane459GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane459GenDeadBlock0
  | ⟨1, _⟩ => exact plane459GenDeadBlock1
  | ⟨2, _⟩ => exact plane459GenDeadBlock2
  | ⟨3, _⟩ => exact plane459GenDeadBlock3
  | ⟨4, _⟩ => exact plane459GenDeadBlock4
  | ⟨5, _⟩ => exact plane459GenDeadBlock5
  | ⟨6, _⟩ => exact plane459GenDeadBlock6
  | ⟨7, _⟩ => exact plane459GenDeadBlock7
  | ⟨8, _⟩ => exact plane459GenDeadBlock8
  | ⟨9, _⟩ => exact plane459GenDeadBlock9
  | ⟨10, _⟩ => exact plane459GenDeadBlock10
  | ⟨11, _⟩ => exact plane459GenDeadBlock11
  | ⟨12, _⟩ => exact plane459GenDeadBlock12
  | ⟨13, _⟩ => exact plane459GenDeadBlock13
  | ⟨14, _⟩ => exact plane459GenDeadBlock14
  | ⟨15, _⟩ => exact plane459GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
