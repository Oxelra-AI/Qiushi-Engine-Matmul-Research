import QiushiPlane419GenDeadBlock0
import QiushiPlane419GenDeadBlock1
import QiushiPlane419GenDeadBlock2
import QiushiPlane419GenDeadBlock3
import QiushiPlane419GenDeadBlock4
import QiushiPlane419GenDeadBlock5
import QiushiPlane419GenDeadBlock6
import QiushiPlane419GenDeadBlock7
import QiushiPlane419GenDeadBlock8
import QiushiPlane419GenDeadBlock9
import QiushiPlane419GenDeadBlock10
import QiushiPlane419GenDeadBlock11
import QiushiPlane419GenDeadBlock12
import QiushiPlane419GenDeadBlock13
import QiushiPlane419GenDeadBlock14
import QiushiPlane419GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane419GenDeadAll : forall i, plane419GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane419GenDeadBlock0
  | ⟨1, _⟩ => exact plane419GenDeadBlock1
  | ⟨2, _⟩ => exact plane419GenDeadBlock2
  | ⟨3, _⟩ => exact plane419GenDeadBlock3
  | ⟨4, _⟩ => exact plane419GenDeadBlock4
  | ⟨5, _⟩ => exact plane419GenDeadBlock5
  | ⟨6, _⟩ => exact plane419GenDeadBlock6
  | ⟨7, _⟩ => exact plane419GenDeadBlock7
  | ⟨8, _⟩ => exact plane419GenDeadBlock8
  | ⟨9, _⟩ => exact plane419GenDeadBlock9
  | ⟨10, _⟩ => exact plane419GenDeadBlock10
  | ⟨11, _⟩ => exact plane419GenDeadBlock11
  | ⟨12, _⟩ => exact plane419GenDeadBlock12
  | ⟨13, _⟩ => exact plane419GenDeadBlock13
  | ⟨14, _⟩ => exact plane419GenDeadBlock14
  | ⟨15, _⟩ => exact plane419GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
