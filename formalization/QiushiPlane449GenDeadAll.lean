import QiushiPlane449GenDeadBlock0
import QiushiPlane449GenDeadBlock1
import QiushiPlane449GenDeadBlock2
import QiushiPlane449GenDeadBlock3
import QiushiPlane449GenDeadBlock4
import QiushiPlane449GenDeadBlock5
import QiushiPlane449GenDeadBlock6
import QiushiPlane449GenDeadBlock7
import QiushiPlane449GenDeadBlock8
import QiushiPlane449GenDeadBlock9
import QiushiPlane449GenDeadBlock10
import QiushiPlane449GenDeadBlock11
import QiushiPlane449GenDeadBlock12
import QiushiPlane449GenDeadBlock13
import QiushiPlane449GenDeadBlock14
import QiushiPlane449GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane449GenDeadAll : forall i, plane449GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane449GenDeadBlock0
  | ⟨1, _⟩ => exact plane449GenDeadBlock1
  | ⟨2, _⟩ => exact plane449GenDeadBlock2
  | ⟨3, _⟩ => exact plane449GenDeadBlock3
  | ⟨4, _⟩ => exact plane449GenDeadBlock4
  | ⟨5, _⟩ => exact plane449GenDeadBlock5
  | ⟨6, _⟩ => exact plane449GenDeadBlock6
  | ⟨7, _⟩ => exact plane449GenDeadBlock7
  | ⟨8, _⟩ => exact plane449GenDeadBlock8
  | ⟨9, _⟩ => exact plane449GenDeadBlock9
  | ⟨10, _⟩ => exact plane449GenDeadBlock10
  | ⟨11, _⟩ => exact plane449GenDeadBlock11
  | ⟨12, _⟩ => exact plane449GenDeadBlock12
  | ⟨13, _⟩ => exact plane449GenDeadBlock13
  | ⟨14, _⟩ => exact plane449GenDeadBlock14
  | ⟨15, _⟩ => exact plane449GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
