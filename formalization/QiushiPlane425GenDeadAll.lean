import QiushiPlane425GenDeadBlock0
import QiushiPlane425GenDeadBlock1
import QiushiPlane425GenDeadBlock2
import QiushiPlane425GenDeadBlock3
import QiushiPlane425GenDeadBlock4
import QiushiPlane425GenDeadBlock5
import QiushiPlane425GenDeadBlock6
import QiushiPlane425GenDeadBlock7
import QiushiPlane425GenDeadBlock8
import QiushiPlane425GenDeadBlock9
import QiushiPlane425GenDeadBlock10
import QiushiPlane425GenDeadBlock11
import QiushiPlane425GenDeadBlock12
import QiushiPlane425GenDeadBlock13
import QiushiPlane425GenDeadBlock14
import QiushiPlane425GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane425GenDeadAll : forall i, plane425GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane425GenDeadBlock0
  | ⟨1, _⟩ => exact plane425GenDeadBlock1
  | ⟨2, _⟩ => exact plane425GenDeadBlock2
  | ⟨3, _⟩ => exact plane425GenDeadBlock3
  | ⟨4, _⟩ => exact plane425GenDeadBlock4
  | ⟨5, _⟩ => exact plane425GenDeadBlock5
  | ⟨6, _⟩ => exact plane425GenDeadBlock6
  | ⟨7, _⟩ => exact plane425GenDeadBlock7
  | ⟨8, _⟩ => exact plane425GenDeadBlock8
  | ⟨9, _⟩ => exact plane425GenDeadBlock9
  | ⟨10, _⟩ => exact plane425GenDeadBlock10
  | ⟨11, _⟩ => exact plane425GenDeadBlock11
  | ⟨12, _⟩ => exact plane425GenDeadBlock12
  | ⟨13, _⟩ => exact plane425GenDeadBlock13
  | ⟨14, _⟩ => exact plane425GenDeadBlock14
  | ⟨15, _⟩ => exact plane425GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
