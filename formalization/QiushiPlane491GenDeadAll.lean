import QiushiPlane491GenDeadBlock0
import QiushiPlane491GenDeadBlock1
import QiushiPlane491GenDeadBlock2
import QiushiPlane491GenDeadBlock3
import QiushiPlane491GenDeadBlock4
import QiushiPlane491GenDeadBlock5
import QiushiPlane491GenDeadBlock6
import QiushiPlane491GenDeadBlock7
import QiushiPlane491GenDeadBlock8
import QiushiPlane491GenDeadBlock9
import QiushiPlane491GenDeadBlock10
import QiushiPlane491GenDeadBlock11
import QiushiPlane491GenDeadBlock12
import QiushiPlane491GenDeadBlock13
import QiushiPlane491GenDeadBlock14
import QiushiPlane491GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane491GenDeadAll : forall i, plane491GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane491GenDeadBlock0
  | ⟨1, _⟩ => exact plane491GenDeadBlock1
  | ⟨2, _⟩ => exact plane491GenDeadBlock2
  | ⟨3, _⟩ => exact plane491GenDeadBlock3
  | ⟨4, _⟩ => exact plane491GenDeadBlock4
  | ⟨5, _⟩ => exact plane491GenDeadBlock5
  | ⟨6, _⟩ => exact plane491GenDeadBlock6
  | ⟨7, _⟩ => exact plane491GenDeadBlock7
  | ⟨8, _⟩ => exact plane491GenDeadBlock8
  | ⟨9, _⟩ => exact plane491GenDeadBlock9
  | ⟨10, _⟩ => exact plane491GenDeadBlock10
  | ⟨11, _⟩ => exact plane491GenDeadBlock11
  | ⟨12, _⟩ => exact plane491GenDeadBlock12
  | ⟨13, _⟩ => exact plane491GenDeadBlock13
  | ⟨14, _⟩ => exact plane491GenDeadBlock14
  | ⟨15, _⟩ => exact plane491GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
