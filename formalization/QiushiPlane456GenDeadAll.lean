import QiushiPlane456GenDeadBlock0
import QiushiPlane456GenDeadBlock1
import QiushiPlane456GenDeadBlock2
import QiushiPlane456GenDeadBlock3
import QiushiPlane456GenDeadBlock4
import QiushiPlane456GenDeadBlock5
import QiushiPlane456GenDeadBlock6
import QiushiPlane456GenDeadBlock7
import QiushiPlane456GenDeadBlock8
import QiushiPlane456GenDeadBlock9
import QiushiPlane456GenDeadBlock10
import QiushiPlane456GenDeadBlock11
import QiushiPlane456GenDeadBlock12
import QiushiPlane456GenDeadBlock13
import QiushiPlane456GenDeadBlock14
import QiushiPlane456GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane456GenDeadAll : forall i, plane456GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane456GenDeadBlock0
  | ⟨1, _⟩ => exact plane456GenDeadBlock1
  | ⟨2, _⟩ => exact plane456GenDeadBlock2
  | ⟨3, _⟩ => exact plane456GenDeadBlock3
  | ⟨4, _⟩ => exact plane456GenDeadBlock4
  | ⟨5, _⟩ => exact plane456GenDeadBlock5
  | ⟨6, _⟩ => exact plane456GenDeadBlock6
  | ⟨7, _⟩ => exact plane456GenDeadBlock7
  | ⟨8, _⟩ => exact plane456GenDeadBlock8
  | ⟨9, _⟩ => exact plane456GenDeadBlock9
  | ⟨10, _⟩ => exact plane456GenDeadBlock10
  | ⟨11, _⟩ => exact plane456GenDeadBlock11
  | ⟨12, _⟩ => exact plane456GenDeadBlock12
  | ⟨13, _⟩ => exact plane456GenDeadBlock13
  | ⟨14, _⟩ => exact plane456GenDeadBlock14
  | ⟨15, _⟩ => exact plane456GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
