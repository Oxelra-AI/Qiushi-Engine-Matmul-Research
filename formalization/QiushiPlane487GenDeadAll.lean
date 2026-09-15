import QiushiPlane487GenDeadBlock0
import QiushiPlane487GenDeadBlock1
import QiushiPlane487GenDeadBlock2
import QiushiPlane487GenDeadBlock3
import QiushiPlane487GenDeadBlock4
import QiushiPlane487GenDeadBlock5
import QiushiPlane487GenDeadBlock6
import QiushiPlane487GenDeadBlock7
import QiushiPlane487GenDeadBlock8
import QiushiPlane487GenDeadBlock9
import QiushiPlane487GenDeadBlock10
import QiushiPlane487GenDeadBlock11
import QiushiPlane487GenDeadBlock12
import QiushiPlane487GenDeadBlock13
import QiushiPlane487GenDeadBlock14
import QiushiPlane487GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane487GenDeadAll : forall i, plane487GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane487GenDeadBlock0
  | ⟨1, _⟩ => exact plane487GenDeadBlock1
  | ⟨2, _⟩ => exact plane487GenDeadBlock2
  | ⟨3, _⟩ => exact plane487GenDeadBlock3
  | ⟨4, _⟩ => exact plane487GenDeadBlock4
  | ⟨5, _⟩ => exact plane487GenDeadBlock5
  | ⟨6, _⟩ => exact plane487GenDeadBlock6
  | ⟨7, _⟩ => exact plane487GenDeadBlock7
  | ⟨8, _⟩ => exact plane487GenDeadBlock8
  | ⟨9, _⟩ => exact plane487GenDeadBlock9
  | ⟨10, _⟩ => exact plane487GenDeadBlock10
  | ⟨11, _⟩ => exact plane487GenDeadBlock11
  | ⟨12, _⟩ => exact plane487GenDeadBlock12
  | ⟨13, _⟩ => exact plane487GenDeadBlock13
  | ⟨14, _⟩ => exact plane487GenDeadBlock14
  | ⟨15, _⟩ => exact plane487GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
