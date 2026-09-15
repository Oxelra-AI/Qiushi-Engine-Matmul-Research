import QiushiPlane489GenDeadBlock0
import QiushiPlane489GenDeadBlock1
import QiushiPlane489GenDeadBlock2
import QiushiPlane489GenDeadBlock3
import QiushiPlane489GenDeadBlock4
import QiushiPlane489GenDeadBlock5
import QiushiPlane489GenDeadBlock6
import QiushiPlane489GenDeadBlock7
import QiushiPlane489GenDeadBlock8
import QiushiPlane489GenDeadBlock9
import QiushiPlane489GenDeadBlock10
import QiushiPlane489GenDeadBlock11
import QiushiPlane489GenDeadBlock12
import QiushiPlane489GenDeadBlock13
import QiushiPlane489GenDeadBlock14
import QiushiPlane489GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane489GenDeadAll : forall i, plane489GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane489GenDeadBlock0
  | ⟨1, _⟩ => exact plane489GenDeadBlock1
  | ⟨2, _⟩ => exact plane489GenDeadBlock2
  | ⟨3, _⟩ => exact plane489GenDeadBlock3
  | ⟨4, _⟩ => exact plane489GenDeadBlock4
  | ⟨5, _⟩ => exact plane489GenDeadBlock5
  | ⟨6, _⟩ => exact plane489GenDeadBlock6
  | ⟨7, _⟩ => exact plane489GenDeadBlock7
  | ⟨8, _⟩ => exact plane489GenDeadBlock8
  | ⟨9, _⟩ => exact plane489GenDeadBlock9
  | ⟨10, _⟩ => exact plane489GenDeadBlock10
  | ⟨11, _⟩ => exact plane489GenDeadBlock11
  | ⟨12, _⟩ => exact plane489GenDeadBlock12
  | ⟨13, _⟩ => exact plane489GenDeadBlock13
  | ⟨14, _⟩ => exact plane489GenDeadBlock14
  | ⟨15, _⟩ => exact plane489GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
