import QiushiPlane466GenDeadBlock0
import QiushiPlane466GenDeadBlock1
import QiushiPlane466GenDeadBlock2
import QiushiPlane466GenDeadBlock3
import QiushiPlane466GenDeadBlock4
import QiushiPlane466GenDeadBlock5
import QiushiPlane466GenDeadBlock6
import QiushiPlane466GenDeadBlock7
import QiushiPlane466GenDeadBlock8
import QiushiPlane466GenDeadBlock9
import QiushiPlane466GenDeadBlock10
import QiushiPlane466GenDeadBlock11
import QiushiPlane466GenDeadBlock12
import QiushiPlane466GenDeadBlock13
import QiushiPlane466GenDeadBlock14
import QiushiPlane466GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane466GenDeadAll : forall i, plane466GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane466GenDeadBlock0
  | ⟨1, _⟩ => exact plane466GenDeadBlock1
  | ⟨2, _⟩ => exact plane466GenDeadBlock2
  | ⟨3, _⟩ => exact plane466GenDeadBlock3
  | ⟨4, _⟩ => exact plane466GenDeadBlock4
  | ⟨5, _⟩ => exact plane466GenDeadBlock5
  | ⟨6, _⟩ => exact plane466GenDeadBlock6
  | ⟨7, _⟩ => exact plane466GenDeadBlock7
  | ⟨8, _⟩ => exact plane466GenDeadBlock8
  | ⟨9, _⟩ => exact plane466GenDeadBlock9
  | ⟨10, _⟩ => exact plane466GenDeadBlock10
  | ⟨11, _⟩ => exact plane466GenDeadBlock11
  | ⟨12, _⟩ => exact plane466GenDeadBlock12
  | ⟨13, _⟩ => exact plane466GenDeadBlock13
  | ⟨14, _⟩ => exact plane466GenDeadBlock14
  | ⟨15, _⟩ => exact plane466GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
