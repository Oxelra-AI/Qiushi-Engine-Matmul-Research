import QiushiPlane426GenDeadBlock0
import QiushiPlane426GenDeadBlock1
import QiushiPlane426GenDeadBlock2
import QiushiPlane426GenDeadBlock3
import QiushiPlane426GenDeadBlock4
import QiushiPlane426GenDeadBlock5
import QiushiPlane426GenDeadBlock6
import QiushiPlane426GenDeadBlock7
import QiushiPlane426GenDeadBlock8
import QiushiPlane426GenDeadBlock9
import QiushiPlane426GenDeadBlock10
import QiushiPlane426GenDeadBlock11
import QiushiPlane426GenDeadBlock12
import QiushiPlane426GenDeadBlock13
import QiushiPlane426GenDeadBlock14
import QiushiPlane426GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane426GenDeadAll : forall i, plane426GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane426GenDeadBlock0
  | ⟨1, _⟩ => exact plane426GenDeadBlock1
  | ⟨2, _⟩ => exact plane426GenDeadBlock2
  | ⟨3, _⟩ => exact plane426GenDeadBlock3
  | ⟨4, _⟩ => exact plane426GenDeadBlock4
  | ⟨5, _⟩ => exact plane426GenDeadBlock5
  | ⟨6, _⟩ => exact plane426GenDeadBlock6
  | ⟨7, _⟩ => exact plane426GenDeadBlock7
  | ⟨8, _⟩ => exact plane426GenDeadBlock8
  | ⟨9, _⟩ => exact plane426GenDeadBlock9
  | ⟨10, _⟩ => exact plane426GenDeadBlock10
  | ⟨11, _⟩ => exact plane426GenDeadBlock11
  | ⟨12, _⟩ => exact plane426GenDeadBlock12
  | ⟨13, _⟩ => exact plane426GenDeadBlock13
  | ⟨14, _⟩ => exact plane426GenDeadBlock14
  | ⟨15, _⟩ => exact plane426GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
