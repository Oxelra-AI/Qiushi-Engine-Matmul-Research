import QiushiPlane477GenDeadBlock0
import QiushiPlane477GenDeadBlock1
import QiushiPlane477GenDeadBlock2
import QiushiPlane477GenDeadBlock3
import QiushiPlane477GenDeadBlock4
import QiushiPlane477GenDeadBlock5
import QiushiPlane477GenDeadBlock6
import QiushiPlane477GenDeadBlock7
import QiushiPlane477GenDeadBlock8
import QiushiPlane477GenDeadBlock9
import QiushiPlane477GenDeadBlock10
import QiushiPlane477GenDeadBlock11
import QiushiPlane477GenDeadBlock12
import QiushiPlane477GenDeadBlock13
import QiushiPlane477GenDeadBlock14
import QiushiPlane477GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane477GenDeadAll : forall i, plane477GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane477GenDeadBlock0
  | ⟨1, _⟩ => exact plane477GenDeadBlock1
  | ⟨2, _⟩ => exact plane477GenDeadBlock2
  | ⟨3, _⟩ => exact plane477GenDeadBlock3
  | ⟨4, _⟩ => exact plane477GenDeadBlock4
  | ⟨5, _⟩ => exact plane477GenDeadBlock5
  | ⟨6, _⟩ => exact plane477GenDeadBlock6
  | ⟨7, _⟩ => exact plane477GenDeadBlock7
  | ⟨8, _⟩ => exact plane477GenDeadBlock8
  | ⟨9, _⟩ => exact plane477GenDeadBlock9
  | ⟨10, _⟩ => exact plane477GenDeadBlock10
  | ⟨11, _⟩ => exact plane477GenDeadBlock11
  | ⟨12, _⟩ => exact plane477GenDeadBlock12
  | ⟨13, _⟩ => exact plane477GenDeadBlock13
  | ⟨14, _⟩ => exact plane477GenDeadBlock14
  | ⟨15, _⟩ => exact plane477GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
