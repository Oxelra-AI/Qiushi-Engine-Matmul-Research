import QiushiPlane255GenDeadBlock0
import QiushiPlane255GenDeadBlock1
import QiushiPlane255GenDeadBlock2
import QiushiPlane255GenDeadBlock3
import QiushiPlane255GenDeadBlock4
import QiushiPlane255GenDeadBlock5
import QiushiPlane255GenDeadBlock6
import QiushiPlane255GenDeadBlock7
import QiushiPlane255GenDeadBlock8
import QiushiPlane255GenDeadBlock9
import QiushiPlane255GenDeadBlock10
import QiushiPlane255GenDeadBlock11
import QiushiPlane255GenDeadBlock12
import QiushiPlane255GenDeadBlock13
import QiushiPlane255GenDeadBlock14
import QiushiPlane255GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane255GenDeadAll : forall i, plane255GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane255GenDeadBlock0
  | ⟨1, _⟩ => exact plane255GenDeadBlock1
  | ⟨2, _⟩ => exact plane255GenDeadBlock2
  | ⟨3, _⟩ => exact plane255GenDeadBlock3
  | ⟨4, _⟩ => exact plane255GenDeadBlock4
  | ⟨5, _⟩ => exact plane255GenDeadBlock5
  | ⟨6, _⟩ => exact plane255GenDeadBlock6
  | ⟨7, _⟩ => exact plane255GenDeadBlock7
  | ⟨8, _⟩ => exact plane255GenDeadBlock8
  | ⟨9, _⟩ => exact plane255GenDeadBlock9
  | ⟨10, _⟩ => exact plane255GenDeadBlock10
  | ⟨11, _⟩ => exact plane255GenDeadBlock11
  | ⟨12, _⟩ => exact plane255GenDeadBlock12
  | ⟨13, _⟩ => exact plane255GenDeadBlock13
  | ⟨14, _⟩ => exact plane255GenDeadBlock14
  | ⟨15, _⟩ => exact plane255GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
