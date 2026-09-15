import QiushiPlane486GenDeadBlock0
import QiushiPlane486GenDeadBlock1
import QiushiPlane486GenDeadBlock2
import QiushiPlane486GenDeadBlock3
import QiushiPlane486GenDeadBlock4
import QiushiPlane486GenDeadBlock5
import QiushiPlane486GenDeadBlock6
import QiushiPlane486GenDeadBlock7
import QiushiPlane486GenDeadBlock8
import QiushiPlane486GenDeadBlock9
import QiushiPlane486GenDeadBlock10
import QiushiPlane486GenDeadBlock11
import QiushiPlane486GenDeadBlock12
import QiushiPlane486GenDeadBlock13
import QiushiPlane486GenDeadBlock14
import QiushiPlane486GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane486GenDeadAll : forall i, plane486GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane486GenDeadBlock0
  | ⟨1, _⟩ => exact plane486GenDeadBlock1
  | ⟨2, _⟩ => exact plane486GenDeadBlock2
  | ⟨3, _⟩ => exact plane486GenDeadBlock3
  | ⟨4, _⟩ => exact plane486GenDeadBlock4
  | ⟨5, _⟩ => exact plane486GenDeadBlock5
  | ⟨6, _⟩ => exact plane486GenDeadBlock6
  | ⟨7, _⟩ => exact plane486GenDeadBlock7
  | ⟨8, _⟩ => exact plane486GenDeadBlock8
  | ⟨9, _⟩ => exact plane486GenDeadBlock9
  | ⟨10, _⟩ => exact plane486GenDeadBlock10
  | ⟨11, _⟩ => exact plane486GenDeadBlock11
  | ⟨12, _⟩ => exact plane486GenDeadBlock12
  | ⟨13, _⟩ => exact plane486GenDeadBlock13
  | ⟨14, _⟩ => exact plane486GenDeadBlock14
  | ⟨15, _⟩ => exact plane486GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
