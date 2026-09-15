import QiushiPlane447GenDeadBlock0
import QiushiPlane447GenDeadBlock1
import QiushiPlane447GenDeadBlock2
import QiushiPlane447GenDeadBlock3
import QiushiPlane447GenDeadBlock4
import QiushiPlane447GenDeadBlock5
import QiushiPlane447GenDeadBlock6
import QiushiPlane447GenDeadBlock7
import QiushiPlane447GenDeadBlock8
import QiushiPlane447GenDeadBlock9
import QiushiPlane447GenDeadBlock10
import QiushiPlane447GenDeadBlock11
import QiushiPlane447GenDeadBlock12
import QiushiPlane447GenDeadBlock13
import QiushiPlane447GenDeadBlock14
import QiushiPlane447GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane447GenDeadAll : forall i, plane447GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane447GenDeadBlock0
  | ⟨1, _⟩ => exact plane447GenDeadBlock1
  | ⟨2, _⟩ => exact plane447GenDeadBlock2
  | ⟨3, _⟩ => exact plane447GenDeadBlock3
  | ⟨4, _⟩ => exact plane447GenDeadBlock4
  | ⟨5, _⟩ => exact plane447GenDeadBlock5
  | ⟨6, _⟩ => exact plane447GenDeadBlock6
  | ⟨7, _⟩ => exact plane447GenDeadBlock7
  | ⟨8, _⟩ => exact plane447GenDeadBlock8
  | ⟨9, _⟩ => exact plane447GenDeadBlock9
  | ⟨10, _⟩ => exact plane447GenDeadBlock10
  | ⟨11, _⟩ => exact plane447GenDeadBlock11
  | ⟨12, _⟩ => exact plane447GenDeadBlock12
  | ⟨13, _⟩ => exact plane447GenDeadBlock13
  | ⟨14, _⟩ => exact plane447GenDeadBlock14
  | ⟨15, _⟩ => exact plane447GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
