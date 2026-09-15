import QiushiPlane338GenDeadBlock0
import QiushiPlane338GenDeadBlock1
import QiushiPlane338GenDeadBlock2
import QiushiPlane338GenDeadBlock3
import QiushiPlane338GenDeadBlock4
import QiushiPlane338GenDeadBlock5
import QiushiPlane338GenDeadBlock6
import QiushiPlane338GenDeadBlock7
import QiushiPlane338GenDeadBlock8
import QiushiPlane338GenDeadBlock9
import QiushiPlane338GenDeadBlock10
import QiushiPlane338GenDeadBlock11
import QiushiPlane338GenDeadBlock12
import QiushiPlane338GenDeadBlock13
import QiushiPlane338GenDeadBlock14
import QiushiPlane338GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane338GenDeadAll : forall i, plane338GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane338GenDeadBlock0
  | ⟨1, _⟩ => exact plane338GenDeadBlock1
  | ⟨2, _⟩ => exact plane338GenDeadBlock2
  | ⟨3, _⟩ => exact plane338GenDeadBlock3
  | ⟨4, _⟩ => exact plane338GenDeadBlock4
  | ⟨5, _⟩ => exact plane338GenDeadBlock5
  | ⟨6, _⟩ => exact plane338GenDeadBlock6
  | ⟨7, _⟩ => exact plane338GenDeadBlock7
  | ⟨8, _⟩ => exact plane338GenDeadBlock8
  | ⟨9, _⟩ => exact plane338GenDeadBlock9
  | ⟨10, _⟩ => exact plane338GenDeadBlock10
  | ⟨11, _⟩ => exact plane338GenDeadBlock11
  | ⟨12, _⟩ => exact plane338GenDeadBlock12
  | ⟨13, _⟩ => exact plane338GenDeadBlock13
  | ⟨14, _⟩ => exact plane338GenDeadBlock14
  | ⟨15, _⟩ => exact plane338GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
