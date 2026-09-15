import QiushiPlane452GenDeadBlock0
import QiushiPlane452GenDeadBlock1
import QiushiPlane452GenDeadBlock2
import QiushiPlane452GenDeadBlock3
import QiushiPlane452GenDeadBlock4
import QiushiPlane452GenDeadBlock5
import QiushiPlane452GenDeadBlock6
import QiushiPlane452GenDeadBlock7
import QiushiPlane452GenDeadBlock8
import QiushiPlane452GenDeadBlock9
import QiushiPlane452GenDeadBlock10
import QiushiPlane452GenDeadBlock11
import QiushiPlane452GenDeadBlock12
import QiushiPlane452GenDeadBlock13
import QiushiPlane452GenDeadBlock14
import QiushiPlane452GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane452GenDeadAll : forall i, plane452GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane452GenDeadBlock0
  | ⟨1, _⟩ => exact plane452GenDeadBlock1
  | ⟨2, _⟩ => exact plane452GenDeadBlock2
  | ⟨3, _⟩ => exact plane452GenDeadBlock3
  | ⟨4, _⟩ => exact plane452GenDeadBlock4
  | ⟨5, _⟩ => exact plane452GenDeadBlock5
  | ⟨6, _⟩ => exact plane452GenDeadBlock6
  | ⟨7, _⟩ => exact plane452GenDeadBlock7
  | ⟨8, _⟩ => exact plane452GenDeadBlock8
  | ⟨9, _⟩ => exact plane452GenDeadBlock9
  | ⟨10, _⟩ => exact plane452GenDeadBlock10
  | ⟨11, _⟩ => exact plane452GenDeadBlock11
  | ⟨12, _⟩ => exact plane452GenDeadBlock12
  | ⟨13, _⟩ => exact plane452GenDeadBlock13
  | ⟨14, _⟩ => exact plane452GenDeadBlock14
  | ⟨15, _⟩ => exact plane452GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
