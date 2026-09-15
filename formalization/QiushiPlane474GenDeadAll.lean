import QiushiPlane474GenDeadBlock0
import QiushiPlane474GenDeadBlock1
import QiushiPlane474GenDeadBlock2
import QiushiPlane474GenDeadBlock3
import QiushiPlane474GenDeadBlock4
import QiushiPlane474GenDeadBlock5
import QiushiPlane474GenDeadBlock6
import QiushiPlane474GenDeadBlock7
import QiushiPlane474GenDeadBlock8
import QiushiPlane474GenDeadBlock9
import QiushiPlane474GenDeadBlock10
import QiushiPlane474GenDeadBlock11
import QiushiPlane474GenDeadBlock12
import QiushiPlane474GenDeadBlock13
import QiushiPlane474GenDeadBlock14
import QiushiPlane474GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane474GenDeadAll : forall i, plane474GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane474GenDeadBlock0
  | ⟨1, _⟩ => exact plane474GenDeadBlock1
  | ⟨2, _⟩ => exact plane474GenDeadBlock2
  | ⟨3, _⟩ => exact plane474GenDeadBlock3
  | ⟨4, _⟩ => exact plane474GenDeadBlock4
  | ⟨5, _⟩ => exact plane474GenDeadBlock5
  | ⟨6, _⟩ => exact plane474GenDeadBlock6
  | ⟨7, _⟩ => exact plane474GenDeadBlock7
  | ⟨8, _⟩ => exact plane474GenDeadBlock8
  | ⟨9, _⟩ => exact plane474GenDeadBlock9
  | ⟨10, _⟩ => exact plane474GenDeadBlock10
  | ⟨11, _⟩ => exact plane474GenDeadBlock11
  | ⟨12, _⟩ => exact plane474GenDeadBlock12
  | ⟨13, _⟩ => exact plane474GenDeadBlock13
  | ⟨14, _⟩ => exact plane474GenDeadBlock14
  | ⟨15, _⟩ => exact plane474GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
