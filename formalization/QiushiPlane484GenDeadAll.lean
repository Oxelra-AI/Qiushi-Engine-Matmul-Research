import QiushiPlane484GenDeadBlock0
import QiushiPlane484GenDeadBlock1
import QiushiPlane484GenDeadBlock2
import QiushiPlane484GenDeadBlock3
import QiushiPlane484GenDeadBlock4
import QiushiPlane484GenDeadBlock5
import QiushiPlane484GenDeadBlock6
import QiushiPlane484GenDeadBlock7
import QiushiPlane484GenDeadBlock8
import QiushiPlane484GenDeadBlock9
import QiushiPlane484GenDeadBlock10
import QiushiPlane484GenDeadBlock11
import QiushiPlane484GenDeadBlock12
import QiushiPlane484GenDeadBlock13
import QiushiPlane484GenDeadBlock14
import QiushiPlane484GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane484GenDeadAll : forall i, plane484GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane484GenDeadBlock0
  | ⟨1, _⟩ => exact plane484GenDeadBlock1
  | ⟨2, _⟩ => exact plane484GenDeadBlock2
  | ⟨3, _⟩ => exact plane484GenDeadBlock3
  | ⟨4, _⟩ => exact plane484GenDeadBlock4
  | ⟨5, _⟩ => exact plane484GenDeadBlock5
  | ⟨6, _⟩ => exact plane484GenDeadBlock6
  | ⟨7, _⟩ => exact plane484GenDeadBlock7
  | ⟨8, _⟩ => exact plane484GenDeadBlock8
  | ⟨9, _⟩ => exact plane484GenDeadBlock9
  | ⟨10, _⟩ => exact plane484GenDeadBlock10
  | ⟨11, _⟩ => exact plane484GenDeadBlock11
  | ⟨12, _⟩ => exact plane484GenDeadBlock12
  | ⟨13, _⟩ => exact plane484GenDeadBlock13
  | ⟨14, _⟩ => exact plane484GenDeadBlock14
  | ⟨15, _⟩ => exact plane484GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
