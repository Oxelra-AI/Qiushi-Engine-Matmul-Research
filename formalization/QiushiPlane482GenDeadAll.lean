import QiushiPlane482GenDeadBlock0
import QiushiPlane482GenDeadBlock1
import QiushiPlane482GenDeadBlock2
import QiushiPlane482GenDeadBlock3
import QiushiPlane482GenDeadBlock4
import QiushiPlane482GenDeadBlock5
import QiushiPlane482GenDeadBlock6
import QiushiPlane482GenDeadBlock7
import QiushiPlane482GenDeadBlock8
import QiushiPlane482GenDeadBlock9
import QiushiPlane482GenDeadBlock10
import QiushiPlane482GenDeadBlock11
import QiushiPlane482GenDeadBlock12
import QiushiPlane482GenDeadBlock13
import QiushiPlane482GenDeadBlock14
import QiushiPlane482GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane482GenDeadAll : forall i, plane482GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane482GenDeadBlock0
  | ⟨1, _⟩ => exact plane482GenDeadBlock1
  | ⟨2, _⟩ => exact plane482GenDeadBlock2
  | ⟨3, _⟩ => exact plane482GenDeadBlock3
  | ⟨4, _⟩ => exact plane482GenDeadBlock4
  | ⟨5, _⟩ => exact plane482GenDeadBlock5
  | ⟨6, _⟩ => exact plane482GenDeadBlock6
  | ⟨7, _⟩ => exact plane482GenDeadBlock7
  | ⟨8, _⟩ => exact plane482GenDeadBlock8
  | ⟨9, _⟩ => exact plane482GenDeadBlock9
  | ⟨10, _⟩ => exact plane482GenDeadBlock10
  | ⟨11, _⟩ => exact plane482GenDeadBlock11
  | ⟨12, _⟩ => exact plane482GenDeadBlock12
  | ⟨13, _⟩ => exact plane482GenDeadBlock13
  | ⟨14, _⟩ => exact plane482GenDeadBlock14
  | ⟨15, _⟩ => exact plane482GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
