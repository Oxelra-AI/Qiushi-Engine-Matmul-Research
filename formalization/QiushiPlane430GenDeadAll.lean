import QiushiPlane430GenDeadBlock0
import QiushiPlane430GenDeadBlock1
import QiushiPlane430GenDeadBlock2
import QiushiPlane430GenDeadBlock3
import QiushiPlane430GenDeadBlock4
import QiushiPlane430GenDeadBlock5
import QiushiPlane430GenDeadBlock6
import QiushiPlane430GenDeadBlock7
import QiushiPlane430GenDeadBlock8
import QiushiPlane430GenDeadBlock9
import QiushiPlane430GenDeadBlock10
import QiushiPlane430GenDeadBlock11
import QiushiPlane430GenDeadBlock12
import QiushiPlane430GenDeadBlock13
import QiushiPlane430GenDeadBlock14
import QiushiPlane430GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane430GenDeadAll : forall i, plane430GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane430GenDeadBlock0
  | ⟨1, _⟩ => exact plane430GenDeadBlock1
  | ⟨2, _⟩ => exact plane430GenDeadBlock2
  | ⟨3, _⟩ => exact plane430GenDeadBlock3
  | ⟨4, _⟩ => exact plane430GenDeadBlock4
  | ⟨5, _⟩ => exact plane430GenDeadBlock5
  | ⟨6, _⟩ => exact plane430GenDeadBlock6
  | ⟨7, _⟩ => exact plane430GenDeadBlock7
  | ⟨8, _⟩ => exact plane430GenDeadBlock8
  | ⟨9, _⟩ => exact plane430GenDeadBlock9
  | ⟨10, _⟩ => exact plane430GenDeadBlock10
  | ⟨11, _⟩ => exact plane430GenDeadBlock11
  | ⟨12, _⟩ => exact plane430GenDeadBlock12
  | ⟨13, _⟩ => exact plane430GenDeadBlock13
  | ⟨14, _⟩ => exact plane430GenDeadBlock14
  | ⟨15, _⟩ => exact plane430GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
