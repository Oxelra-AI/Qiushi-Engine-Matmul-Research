import QiushiPlane481GenDeadBlock0
import QiushiPlane481GenDeadBlock1
import QiushiPlane481GenDeadBlock2
import QiushiPlane481GenDeadBlock3
import QiushiPlane481GenDeadBlock4
import QiushiPlane481GenDeadBlock5
import QiushiPlane481GenDeadBlock6
import QiushiPlane481GenDeadBlock7
import QiushiPlane481GenDeadBlock8
import QiushiPlane481GenDeadBlock9
import QiushiPlane481GenDeadBlock10
import QiushiPlane481GenDeadBlock11
import QiushiPlane481GenDeadBlock12
import QiushiPlane481GenDeadBlock13
import QiushiPlane481GenDeadBlock14
import QiushiPlane481GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane481GenDeadAll : forall i, plane481GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane481GenDeadBlock0
  | ⟨1, _⟩ => exact plane481GenDeadBlock1
  | ⟨2, _⟩ => exact plane481GenDeadBlock2
  | ⟨3, _⟩ => exact plane481GenDeadBlock3
  | ⟨4, _⟩ => exact plane481GenDeadBlock4
  | ⟨5, _⟩ => exact plane481GenDeadBlock5
  | ⟨6, _⟩ => exact plane481GenDeadBlock6
  | ⟨7, _⟩ => exact plane481GenDeadBlock7
  | ⟨8, _⟩ => exact plane481GenDeadBlock8
  | ⟨9, _⟩ => exact plane481GenDeadBlock9
  | ⟨10, _⟩ => exact plane481GenDeadBlock10
  | ⟨11, _⟩ => exact plane481GenDeadBlock11
  | ⟨12, _⟩ => exact plane481GenDeadBlock12
  | ⟨13, _⟩ => exact plane481GenDeadBlock13
  | ⟨14, _⟩ => exact plane481GenDeadBlock14
  | ⟨15, _⟩ => exact plane481GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
