import QiushiPlane468GenDeadBlock0
import QiushiPlane468GenDeadBlock1
import QiushiPlane468GenDeadBlock2
import QiushiPlane468GenDeadBlock3
import QiushiPlane468GenDeadBlock4
import QiushiPlane468GenDeadBlock5
import QiushiPlane468GenDeadBlock6
import QiushiPlane468GenDeadBlock7
import QiushiPlane468GenDeadBlock8
import QiushiPlane468GenDeadBlock9
import QiushiPlane468GenDeadBlock10
import QiushiPlane468GenDeadBlock11
import QiushiPlane468GenDeadBlock12
import QiushiPlane468GenDeadBlock13
import QiushiPlane468GenDeadBlock14
import QiushiPlane468GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane468GenDeadAll : forall i, plane468GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane468GenDeadBlock0
  | ⟨1, _⟩ => exact plane468GenDeadBlock1
  | ⟨2, _⟩ => exact plane468GenDeadBlock2
  | ⟨3, _⟩ => exact plane468GenDeadBlock3
  | ⟨4, _⟩ => exact plane468GenDeadBlock4
  | ⟨5, _⟩ => exact plane468GenDeadBlock5
  | ⟨6, _⟩ => exact plane468GenDeadBlock6
  | ⟨7, _⟩ => exact plane468GenDeadBlock7
  | ⟨8, _⟩ => exact plane468GenDeadBlock8
  | ⟨9, _⟩ => exact plane468GenDeadBlock9
  | ⟨10, _⟩ => exact plane468GenDeadBlock10
  | ⟨11, _⟩ => exact plane468GenDeadBlock11
  | ⟨12, _⟩ => exact plane468GenDeadBlock12
  | ⟨13, _⟩ => exact plane468GenDeadBlock13
  | ⟨14, _⟩ => exact plane468GenDeadBlock14
  | ⟨15, _⟩ => exact plane468GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
