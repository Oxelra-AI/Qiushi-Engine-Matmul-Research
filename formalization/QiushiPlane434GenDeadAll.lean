import QiushiPlane434GenDeadBlock0
import QiushiPlane434GenDeadBlock1
import QiushiPlane434GenDeadBlock2
import QiushiPlane434GenDeadBlock3
import QiushiPlane434GenDeadBlock4
import QiushiPlane434GenDeadBlock5
import QiushiPlane434GenDeadBlock6
import QiushiPlane434GenDeadBlock7
import QiushiPlane434GenDeadBlock8
import QiushiPlane434GenDeadBlock9
import QiushiPlane434GenDeadBlock10
import QiushiPlane434GenDeadBlock11
import QiushiPlane434GenDeadBlock12
import QiushiPlane434GenDeadBlock13
import QiushiPlane434GenDeadBlock14
import QiushiPlane434GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane434GenDeadAll : forall i, plane434GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane434GenDeadBlock0
  | ⟨1, _⟩ => exact plane434GenDeadBlock1
  | ⟨2, _⟩ => exact plane434GenDeadBlock2
  | ⟨3, _⟩ => exact plane434GenDeadBlock3
  | ⟨4, _⟩ => exact plane434GenDeadBlock4
  | ⟨5, _⟩ => exact plane434GenDeadBlock5
  | ⟨6, _⟩ => exact plane434GenDeadBlock6
  | ⟨7, _⟩ => exact plane434GenDeadBlock7
  | ⟨8, _⟩ => exact plane434GenDeadBlock8
  | ⟨9, _⟩ => exact plane434GenDeadBlock9
  | ⟨10, _⟩ => exact plane434GenDeadBlock10
  | ⟨11, _⟩ => exact plane434GenDeadBlock11
  | ⟨12, _⟩ => exact plane434GenDeadBlock12
  | ⟨13, _⟩ => exact plane434GenDeadBlock13
  | ⟨14, _⟩ => exact plane434GenDeadBlock14
  | ⟨15, _⟩ => exact plane434GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
