import QiushiPlane458GenDeadBlock0
import QiushiPlane458GenDeadBlock1
import QiushiPlane458GenDeadBlock2
import QiushiPlane458GenDeadBlock3
import QiushiPlane458GenDeadBlock4
import QiushiPlane458GenDeadBlock5
import QiushiPlane458GenDeadBlock6
import QiushiPlane458GenDeadBlock7
import QiushiPlane458GenDeadBlock8
import QiushiPlane458GenDeadBlock9
import QiushiPlane458GenDeadBlock10
import QiushiPlane458GenDeadBlock11
import QiushiPlane458GenDeadBlock12
import QiushiPlane458GenDeadBlock13
import QiushiPlane458GenDeadBlock14
import QiushiPlane458GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane458GenDeadAll : forall i, plane458GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane458GenDeadBlock0
  | ⟨1, _⟩ => exact plane458GenDeadBlock1
  | ⟨2, _⟩ => exact plane458GenDeadBlock2
  | ⟨3, _⟩ => exact plane458GenDeadBlock3
  | ⟨4, _⟩ => exact plane458GenDeadBlock4
  | ⟨5, _⟩ => exact plane458GenDeadBlock5
  | ⟨6, _⟩ => exact plane458GenDeadBlock6
  | ⟨7, _⟩ => exact plane458GenDeadBlock7
  | ⟨8, _⟩ => exact plane458GenDeadBlock8
  | ⟨9, _⟩ => exact plane458GenDeadBlock9
  | ⟨10, _⟩ => exact plane458GenDeadBlock10
  | ⟨11, _⟩ => exact plane458GenDeadBlock11
  | ⟨12, _⟩ => exact plane458GenDeadBlock12
  | ⟨13, _⟩ => exact plane458GenDeadBlock13
  | ⟨14, _⟩ => exact plane458GenDeadBlock14
  | ⟨15, _⟩ => exact plane458GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
