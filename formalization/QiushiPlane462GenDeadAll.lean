import QiushiPlane462GenDeadBlock0
import QiushiPlane462GenDeadBlock1
import QiushiPlane462GenDeadBlock2
import QiushiPlane462GenDeadBlock3
import QiushiPlane462GenDeadBlock4
import QiushiPlane462GenDeadBlock5
import QiushiPlane462GenDeadBlock6
import QiushiPlane462GenDeadBlock7
import QiushiPlane462GenDeadBlock8
import QiushiPlane462GenDeadBlock9
import QiushiPlane462GenDeadBlock10
import QiushiPlane462GenDeadBlock11
import QiushiPlane462GenDeadBlock12
import QiushiPlane462GenDeadBlock13
import QiushiPlane462GenDeadBlock14
import QiushiPlane462GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane462GenDeadAll : forall i, plane462GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane462GenDeadBlock0
  | ⟨1, _⟩ => exact plane462GenDeadBlock1
  | ⟨2, _⟩ => exact plane462GenDeadBlock2
  | ⟨3, _⟩ => exact plane462GenDeadBlock3
  | ⟨4, _⟩ => exact plane462GenDeadBlock4
  | ⟨5, _⟩ => exact plane462GenDeadBlock5
  | ⟨6, _⟩ => exact plane462GenDeadBlock6
  | ⟨7, _⟩ => exact plane462GenDeadBlock7
  | ⟨8, _⟩ => exact plane462GenDeadBlock8
  | ⟨9, _⟩ => exact plane462GenDeadBlock9
  | ⟨10, _⟩ => exact plane462GenDeadBlock10
  | ⟨11, _⟩ => exact plane462GenDeadBlock11
  | ⟨12, _⟩ => exact plane462GenDeadBlock12
  | ⟨13, _⟩ => exact plane462GenDeadBlock13
  | ⟨14, _⟩ => exact plane462GenDeadBlock14
  | ⟨15, _⟩ => exact plane462GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
