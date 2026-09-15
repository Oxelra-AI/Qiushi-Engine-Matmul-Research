import QiushiPlane490GenDeadBlock0
import QiushiPlane490GenDeadBlock1
import QiushiPlane490GenDeadBlock2
import QiushiPlane490GenDeadBlock3
import QiushiPlane490GenDeadBlock4
import QiushiPlane490GenDeadBlock5
import QiushiPlane490GenDeadBlock6
import QiushiPlane490GenDeadBlock7
import QiushiPlane490GenDeadBlock8
import QiushiPlane490GenDeadBlock9
import QiushiPlane490GenDeadBlock10
import QiushiPlane490GenDeadBlock11
import QiushiPlane490GenDeadBlock12
import QiushiPlane490GenDeadBlock13
import QiushiPlane490GenDeadBlock14
import QiushiPlane490GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane490GenDeadAll : forall i, plane490GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane490GenDeadBlock0
  | ⟨1, _⟩ => exact plane490GenDeadBlock1
  | ⟨2, _⟩ => exact plane490GenDeadBlock2
  | ⟨3, _⟩ => exact plane490GenDeadBlock3
  | ⟨4, _⟩ => exact plane490GenDeadBlock4
  | ⟨5, _⟩ => exact plane490GenDeadBlock5
  | ⟨6, _⟩ => exact plane490GenDeadBlock6
  | ⟨7, _⟩ => exact plane490GenDeadBlock7
  | ⟨8, _⟩ => exact plane490GenDeadBlock8
  | ⟨9, _⟩ => exact plane490GenDeadBlock9
  | ⟨10, _⟩ => exact plane490GenDeadBlock10
  | ⟨11, _⟩ => exact plane490GenDeadBlock11
  | ⟨12, _⟩ => exact plane490GenDeadBlock12
  | ⟨13, _⟩ => exact plane490GenDeadBlock13
  | ⟨14, _⟩ => exact plane490GenDeadBlock14
  | ⟨15, _⟩ => exact plane490GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
