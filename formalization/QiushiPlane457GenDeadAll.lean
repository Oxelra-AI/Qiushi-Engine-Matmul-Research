import QiushiPlane457GenDeadBlock0
import QiushiPlane457GenDeadBlock1
import QiushiPlane457GenDeadBlock2
import QiushiPlane457GenDeadBlock3
import QiushiPlane457GenDeadBlock4
import QiushiPlane457GenDeadBlock5
import QiushiPlane457GenDeadBlock6
import QiushiPlane457GenDeadBlock7
import QiushiPlane457GenDeadBlock8
import QiushiPlane457GenDeadBlock9
import QiushiPlane457GenDeadBlock10
import QiushiPlane457GenDeadBlock11
import QiushiPlane457GenDeadBlock12
import QiushiPlane457GenDeadBlock13
import QiushiPlane457GenDeadBlock14
import QiushiPlane457GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane457GenDeadAll : forall i, plane457GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane457GenDeadBlock0
  | ⟨1, _⟩ => exact plane457GenDeadBlock1
  | ⟨2, _⟩ => exact plane457GenDeadBlock2
  | ⟨3, _⟩ => exact plane457GenDeadBlock3
  | ⟨4, _⟩ => exact plane457GenDeadBlock4
  | ⟨5, _⟩ => exact plane457GenDeadBlock5
  | ⟨6, _⟩ => exact plane457GenDeadBlock6
  | ⟨7, _⟩ => exact plane457GenDeadBlock7
  | ⟨8, _⟩ => exact plane457GenDeadBlock8
  | ⟨9, _⟩ => exact plane457GenDeadBlock9
  | ⟨10, _⟩ => exact plane457GenDeadBlock10
  | ⟨11, _⟩ => exact plane457GenDeadBlock11
  | ⟨12, _⟩ => exact plane457GenDeadBlock12
  | ⟨13, _⟩ => exact plane457GenDeadBlock13
  | ⟨14, _⟩ => exact plane457GenDeadBlock14
  | ⟨15, _⟩ => exact plane457GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
