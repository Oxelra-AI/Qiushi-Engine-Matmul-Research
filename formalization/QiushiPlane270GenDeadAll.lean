import QiushiPlane270GenDeadBlock0
import QiushiPlane270GenDeadBlock1
import QiushiPlane270GenDeadBlock2
import QiushiPlane270GenDeadBlock3
import QiushiPlane270GenDeadBlock4
import QiushiPlane270GenDeadBlock5
import QiushiPlane270GenDeadBlock6
import QiushiPlane270GenDeadBlock7
import QiushiPlane270GenDeadBlock8
import QiushiPlane270GenDeadBlock9
import QiushiPlane270GenDeadBlock10
import QiushiPlane270GenDeadBlock11
import QiushiPlane270GenDeadBlock12
import QiushiPlane270GenDeadBlock13
import QiushiPlane270GenDeadBlock14
import QiushiPlane270GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane270GenDeadAll : forall i, plane270GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane270GenDeadBlock0
  | ⟨1, _⟩ => exact plane270GenDeadBlock1
  | ⟨2, _⟩ => exact plane270GenDeadBlock2
  | ⟨3, _⟩ => exact plane270GenDeadBlock3
  | ⟨4, _⟩ => exact plane270GenDeadBlock4
  | ⟨5, _⟩ => exact plane270GenDeadBlock5
  | ⟨6, _⟩ => exact plane270GenDeadBlock6
  | ⟨7, _⟩ => exact plane270GenDeadBlock7
  | ⟨8, _⟩ => exact plane270GenDeadBlock8
  | ⟨9, _⟩ => exact plane270GenDeadBlock9
  | ⟨10, _⟩ => exact plane270GenDeadBlock10
  | ⟨11, _⟩ => exact plane270GenDeadBlock11
  | ⟨12, _⟩ => exact plane270GenDeadBlock12
  | ⟨13, _⟩ => exact plane270GenDeadBlock13
  | ⟨14, _⟩ => exact plane270GenDeadBlock14
  | ⟨15, _⟩ => exact plane270GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
