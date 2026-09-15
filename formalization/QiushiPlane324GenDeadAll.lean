import QiushiPlane324GenDeadBlock0
import QiushiPlane324GenDeadBlock1
import QiushiPlane324GenDeadBlock2
import QiushiPlane324GenDeadBlock3
import QiushiPlane324GenDeadBlock4
import QiushiPlane324GenDeadBlock5
import QiushiPlane324GenDeadBlock6
import QiushiPlane324GenDeadBlock7
import QiushiPlane324GenDeadBlock8
import QiushiPlane324GenDeadBlock9
import QiushiPlane324GenDeadBlock10
import QiushiPlane324GenDeadBlock11
import QiushiPlane324GenDeadBlock12
import QiushiPlane324GenDeadBlock13
import QiushiPlane324GenDeadBlock14
import QiushiPlane324GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane324GenDeadAll : forall i, plane324GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane324GenDeadBlock0
  | ⟨1, _⟩ => exact plane324GenDeadBlock1
  | ⟨2, _⟩ => exact plane324GenDeadBlock2
  | ⟨3, _⟩ => exact plane324GenDeadBlock3
  | ⟨4, _⟩ => exact plane324GenDeadBlock4
  | ⟨5, _⟩ => exact plane324GenDeadBlock5
  | ⟨6, _⟩ => exact plane324GenDeadBlock6
  | ⟨7, _⟩ => exact plane324GenDeadBlock7
  | ⟨8, _⟩ => exact plane324GenDeadBlock8
  | ⟨9, _⟩ => exact plane324GenDeadBlock9
  | ⟨10, _⟩ => exact plane324GenDeadBlock10
  | ⟨11, _⟩ => exact plane324GenDeadBlock11
  | ⟨12, _⟩ => exact plane324GenDeadBlock12
  | ⟨13, _⟩ => exact plane324GenDeadBlock13
  | ⟨14, _⟩ => exact plane324GenDeadBlock14
  | ⟨15, _⟩ => exact plane324GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
