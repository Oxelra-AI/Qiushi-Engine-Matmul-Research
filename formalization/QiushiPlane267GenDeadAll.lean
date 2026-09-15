import QiushiPlane267GenDeadBlock0
import QiushiPlane267GenDeadBlock1
import QiushiPlane267GenDeadBlock2
import QiushiPlane267GenDeadBlock3
import QiushiPlane267GenDeadBlock4
import QiushiPlane267GenDeadBlock5
import QiushiPlane267GenDeadBlock6
import QiushiPlane267GenDeadBlock7
import QiushiPlane267GenDeadBlock8
import QiushiPlane267GenDeadBlock9
import QiushiPlane267GenDeadBlock10
import QiushiPlane267GenDeadBlock11
import QiushiPlane267GenDeadBlock12
import QiushiPlane267GenDeadBlock13
import QiushiPlane267GenDeadBlock14
import QiushiPlane267GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane267GenDeadAll : forall i, plane267GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane267GenDeadBlock0
  | ⟨1, _⟩ => exact plane267GenDeadBlock1
  | ⟨2, _⟩ => exact plane267GenDeadBlock2
  | ⟨3, _⟩ => exact plane267GenDeadBlock3
  | ⟨4, _⟩ => exact plane267GenDeadBlock4
  | ⟨5, _⟩ => exact plane267GenDeadBlock5
  | ⟨6, _⟩ => exact plane267GenDeadBlock6
  | ⟨7, _⟩ => exact plane267GenDeadBlock7
  | ⟨8, _⟩ => exact plane267GenDeadBlock8
  | ⟨9, _⟩ => exact plane267GenDeadBlock9
  | ⟨10, _⟩ => exact plane267GenDeadBlock10
  | ⟨11, _⟩ => exact plane267GenDeadBlock11
  | ⟨12, _⟩ => exact plane267GenDeadBlock12
  | ⟨13, _⟩ => exact plane267GenDeadBlock13
  | ⟨14, _⟩ => exact plane267GenDeadBlock14
  | ⟨15, _⟩ => exact plane267GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
