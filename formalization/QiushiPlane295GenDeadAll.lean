import QiushiPlane295GenDeadBlock0
import QiushiPlane295GenDeadBlock1
import QiushiPlane295GenDeadBlock2
import QiushiPlane295GenDeadBlock3
import QiushiPlane295GenDeadBlock4
import QiushiPlane295GenDeadBlock5
import QiushiPlane295GenDeadBlock6
import QiushiPlane295GenDeadBlock7
import QiushiPlane295GenDeadBlock8
import QiushiPlane295GenDeadBlock9
import QiushiPlane295GenDeadBlock10
import QiushiPlane295GenDeadBlock11
import QiushiPlane295GenDeadBlock12
import QiushiPlane295GenDeadBlock13
import QiushiPlane295GenDeadBlock14
import QiushiPlane295GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane295GenDeadAll : forall i, plane295GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane295GenDeadBlock0
  | ⟨1, _⟩ => exact plane295GenDeadBlock1
  | ⟨2, _⟩ => exact plane295GenDeadBlock2
  | ⟨3, _⟩ => exact plane295GenDeadBlock3
  | ⟨4, _⟩ => exact plane295GenDeadBlock4
  | ⟨5, _⟩ => exact plane295GenDeadBlock5
  | ⟨6, _⟩ => exact plane295GenDeadBlock6
  | ⟨7, _⟩ => exact plane295GenDeadBlock7
  | ⟨8, _⟩ => exact plane295GenDeadBlock8
  | ⟨9, _⟩ => exact plane295GenDeadBlock9
  | ⟨10, _⟩ => exact plane295GenDeadBlock10
  | ⟨11, _⟩ => exact plane295GenDeadBlock11
  | ⟨12, _⟩ => exact plane295GenDeadBlock12
  | ⟨13, _⟩ => exact plane295GenDeadBlock13
  | ⟨14, _⟩ => exact plane295GenDeadBlock14
  | ⟨15, _⟩ => exact plane295GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
