import QiushiPlane428GenDeadBlock0
import QiushiPlane428GenDeadBlock1
import QiushiPlane428GenDeadBlock2
import QiushiPlane428GenDeadBlock3
import QiushiPlane428GenDeadBlock4
import QiushiPlane428GenDeadBlock5
import QiushiPlane428GenDeadBlock6
import QiushiPlane428GenDeadBlock7
import QiushiPlane428GenDeadBlock8
import QiushiPlane428GenDeadBlock9
import QiushiPlane428GenDeadBlock10
import QiushiPlane428GenDeadBlock11
import QiushiPlane428GenDeadBlock12
import QiushiPlane428GenDeadBlock13
import QiushiPlane428GenDeadBlock14
import QiushiPlane428GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane428GenDeadAll : forall i, plane428GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane428GenDeadBlock0
  | ⟨1, _⟩ => exact plane428GenDeadBlock1
  | ⟨2, _⟩ => exact plane428GenDeadBlock2
  | ⟨3, _⟩ => exact plane428GenDeadBlock3
  | ⟨4, _⟩ => exact plane428GenDeadBlock4
  | ⟨5, _⟩ => exact plane428GenDeadBlock5
  | ⟨6, _⟩ => exact plane428GenDeadBlock6
  | ⟨7, _⟩ => exact plane428GenDeadBlock7
  | ⟨8, _⟩ => exact plane428GenDeadBlock8
  | ⟨9, _⟩ => exact plane428GenDeadBlock9
  | ⟨10, _⟩ => exact plane428GenDeadBlock10
  | ⟨11, _⟩ => exact plane428GenDeadBlock11
  | ⟨12, _⟩ => exact plane428GenDeadBlock12
  | ⟨13, _⟩ => exact plane428GenDeadBlock13
  | ⟨14, _⟩ => exact plane428GenDeadBlock14
  | ⟨15, _⟩ => exact plane428GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
