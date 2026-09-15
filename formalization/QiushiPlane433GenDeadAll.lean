import QiushiPlane433GenDeadBlock0
import QiushiPlane433GenDeadBlock1
import QiushiPlane433GenDeadBlock2
import QiushiPlane433GenDeadBlock3
import QiushiPlane433GenDeadBlock4
import QiushiPlane433GenDeadBlock5
import QiushiPlane433GenDeadBlock6
import QiushiPlane433GenDeadBlock7
import QiushiPlane433GenDeadBlock8
import QiushiPlane433GenDeadBlock9
import QiushiPlane433GenDeadBlock10
import QiushiPlane433GenDeadBlock11
import QiushiPlane433GenDeadBlock12
import QiushiPlane433GenDeadBlock13
import QiushiPlane433GenDeadBlock14
import QiushiPlane433GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane433GenDeadAll : forall i, plane433GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane433GenDeadBlock0
  | ⟨1, _⟩ => exact plane433GenDeadBlock1
  | ⟨2, _⟩ => exact plane433GenDeadBlock2
  | ⟨3, _⟩ => exact plane433GenDeadBlock3
  | ⟨4, _⟩ => exact plane433GenDeadBlock4
  | ⟨5, _⟩ => exact plane433GenDeadBlock5
  | ⟨6, _⟩ => exact plane433GenDeadBlock6
  | ⟨7, _⟩ => exact plane433GenDeadBlock7
  | ⟨8, _⟩ => exact plane433GenDeadBlock8
  | ⟨9, _⟩ => exact plane433GenDeadBlock9
  | ⟨10, _⟩ => exact plane433GenDeadBlock10
  | ⟨11, _⟩ => exact plane433GenDeadBlock11
  | ⟨12, _⟩ => exact plane433GenDeadBlock12
  | ⟨13, _⟩ => exact plane433GenDeadBlock13
  | ⟨14, _⟩ => exact plane433GenDeadBlock14
  | ⟨15, _⟩ => exact plane433GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
