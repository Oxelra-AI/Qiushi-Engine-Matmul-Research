import QiushiPlane467GenDeadBlock0
import QiushiPlane467GenDeadBlock1
import QiushiPlane467GenDeadBlock2
import QiushiPlane467GenDeadBlock3
import QiushiPlane467GenDeadBlock4
import QiushiPlane467GenDeadBlock5
import QiushiPlane467GenDeadBlock6
import QiushiPlane467GenDeadBlock7
import QiushiPlane467GenDeadBlock8
import QiushiPlane467GenDeadBlock9
import QiushiPlane467GenDeadBlock10
import QiushiPlane467GenDeadBlock11
import QiushiPlane467GenDeadBlock12
import QiushiPlane467GenDeadBlock13
import QiushiPlane467GenDeadBlock14
import QiushiPlane467GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane467GenDeadAll : forall i, plane467GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane467GenDeadBlock0
  | ⟨1, _⟩ => exact plane467GenDeadBlock1
  | ⟨2, _⟩ => exact plane467GenDeadBlock2
  | ⟨3, _⟩ => exact plane467GenDeadBlock3
  | ⟨4, _⟩ => exact plane467GenDeadBlock4
  | ⟨5, _⟩ => exact plane467GenDeadBlock5
  | ⟨6, _⟩ => exact plane467GenDeadBlock6
  | ⟨7, _⟩ => exact plane467GenDeadBlock7
  | ⟨8, _⟩ => exact plane467GenDeadBlock8
  | ⟨9, _⟩ => exact plane467GenDeadBlock9
  | ⟨10, _⟩ => exact plane467GenDeadBlock10
  | ⟨11, _⟩ => exact plane467GenDeadBlock11
  | ⟨12, _⟩ => exact plane467GenDeadBlock12
  | ⟨13, _⟩ => exact plane467GenDeadBlock13
  | ⟨14, _⟩ => exact plane467GenDeadBlock14
  | ⟨15, _⟩ => exact plane467GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
