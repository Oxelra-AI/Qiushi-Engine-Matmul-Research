import QiushiPlane464GenDeadBlock0
import QiushiPlane464GenDeadBlock1
import QiushiPlane464GenDeadBlock2
import QiushiPlane464GenDeadBlock3
import QiushiPlane464GenDeadBlock4
import QiushiPlane464GenDeadBlock5
import QiushiPlane464GenDeadBlock6
import QiushiPlane464GenDeadBlock7
import QiushiPlane464GenDeadBlock8
import QiushiPlane464GenDeadBlock9
import QiushiPlane464GenDeadBlock10
import QiushiPlane464GenDeadBlock11
import QiushiPlane464GenDeadBlock12
import QiushiPlane464GenDeadBlock13
import QiushiPlane464GenDeadBlock14
import QiushiPlane464GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane464GenDeadAll : forall i, plane464GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane464GenDeadBlock0
  | ⟨1, _⟩ => exact plane464GenDeadBlock1
  | ⟨2, _⟩ => exact plane464GenDeadBlock2
  | ⟨3, _⟩ => exact plane464GenDeadBlock3
  | ⟨4, _⟩ => exact plane464GenDeadBlock4
  | ⟨5, _⟩ => exact plane464GenDeadBlock5
  | ⟨6, _⟩ => exact plane464GenDeadBlock6
  | ⟨7, _⟩ => exact plane464GenDeadBlock7
  | ⟨8, _⟩ => exact plane464GenDeadBlock8
  | ⟨9, _⟩ => exact plane464GenDeadBlock9
  | ⟨10, _⟩ => exact plane464GenDeadBlock10
  | ⟨11, _⟩ => exact plane464GenDeadBlock11
  | ⟨12, _⟩ => exact plane464GenDeadBlock12
  | ⟨13, _⟩ => exact plane464GenDeadBlock13
  | ⟨14, _⟩ => exact plane464GenDeadBlock14
  | ⟨15, _⟩ => exact plane464GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
