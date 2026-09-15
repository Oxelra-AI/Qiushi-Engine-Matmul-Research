import QiushiPlane315GenDeadBlock0
import QiushiPlane315GenDeadBlock1
import QiushiPlane315GenDeadBlock2
import QiushiPlane315GenDeadBlock3
import QiushiPlane315GenDeadBlock4
import QiushiPlane315GenDeadBlock5
import QiushiPlane315GenDeadBlock6
import QiushiPlane315GenDeadBlock7
import QiushiPlane315GenDeadBlock8
import QiushiPlane315GenDeadBlock9
import QiushiPlane315GenDeadBlock10
import QiushiPlane315GenDeadBlock11
import QiushiPlane315GenDeadBlock12
import QiushiPlane315GenDeadBlock13
import QiushiPlane315GenDeadBlock14
import QiushiPlane315GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane315GenDeadAll : forall i, plane315GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane315GenDeadBlock0
  | ⟨1, _⟩ => exact plane315GenDeadBlock1
  | ⟨2, _⟩ => exact plane315GenDeadBlock2
  | ⟨3, _⟩ => exact plane315GenDeadBlock3
  | ⟨4, _⟩ => exact plane315GenDeadBlock4
  | ⟨5, _⟩ => exact plane315GenDeadBlock5
  | ⟨6, _⟩ => exact plane315GenDeadBlock6
  | ⟨7, _⟩ => exact plane315GenDeadBlock7
  | ⟨8, _⟩ => exact plane315GenDeadBlock8
  | ⟨9, _⟩ => exact plane315GenDeadBlock9
  | ⟨10, _⟩ => exact plane315GenDeadBlock10
  | ⟨11, _⟩ => exact plane315GenDeadBlock11
  | ⟨12, _⟩ => exact plane315GenDeadBlock12
  | ⟨13, _⟩ => exact plane315GenDeadBlock13
  | ⟨14, _⟩ => exact plane315GenDeadBlock14
  | ⟨15, _⟩ => exact plane315GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
