import QiushiPlane471GenDeadBlock0
import QiushiPlane471GenDeadBlock1
import QiushiPlane471GenDeadBlock2
import QiushiPlane471GenDeadBlock3
import QiushiPlane471GenDeadBlock4
import QiushiPlane471GenDeadBlock5
import QiushiPlane471GenDeadBlock6
import QiushiPlane471GenDeadBlock7
import QiushiPlane471GenDeadBlock8
import QiushiPlane471GenDeadBlock9
import QiushiPlane471GenDeadBlock10
import QiushiPlane471GenDeadBlock11
import QiushiPlane471GenDeadBlock12
import QiushiPlane471GenDeadBlock13
import QiushiPlane471GenDeadBlock14
import QiushiPlane471GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane471GenDeadAll : forall i, plane471GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane471GenDeadBlock0
  | ⟨1, _⟩ => exact plane471GenDeadBlock1
  | ⟨2, _⟩ => exact plane471GenDeadBlock2
  | ⟨3, _⟩ => exact plane471GenDeadBlock3
  | ⟨4, _⟩ => exact plane471GenDeadBlock4
  | ⟨5, _⟩ => exact plane471GenDeadBlock5
  | ⟨6, _⟩ => exact plane471GenDeadBlock6
  | ⟨7, _⟩ => exact plane471GenDeadBlock7
  | ⟨8, _⟩ => exact plane471GenDeadBlock8
  | ⟨9, _⟩ => exact plane471GenDeadBlock9
  | ⟨10, _⟩ => exact plane471GenDeadBlock10
  | ⟨11, _⟩ => exact plane471GenDeadBlock11
  | ⟨12, _⟩ => exact plane471GenDeadBlock12
  | ⟨13, _⟩ => exact plane471GenDeadBlock13
  | ⟨14, _⟩ => exact plane471GenDeadBlock14
  | ⟨15, _⟩ => exact plane471GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
