import QiushiPlane476GenDeadBlock0
import QiushiPlane476GenDeadBlock1
import QiushiPlane476GenDeadBlock2
import QiushiPlane476GenDeadBlock3
import QiushiPlane476GenDeadBlock4
import QiushiPlane476GenDeadBlock5
import QiushiPlane476GenDeadBlock6
import QiushiPlane476GenDeadBlock7
import QiushiPlane476GenDeadBlock8
import QiushiPlane476GenDeadBlock9
import QiushiPlane476GenDeadBlock10
import QiushiPlane476GenDeadBlock11
import QiushiPlane476GenDeadBlock12
import QiushiPlane476GenDeadBlock13
import QiushiPlane476GenDeadBlock14
import QiushiPlane476GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane476GenDeadAll : forall i, plane476GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane476GenDeadBlock0
  | ⟨1, _⟩ => exact plane476GenDeadBlock1
  | ⟨2, _⟩ => exact plane476GenDeadBlock2
  | ⟨3, _⟩ => exact plane476GenDeadBlock3
  | ⟨4, _⟩ => exact plane476GenDeadBlock4
  | ⟨5, _⟩ => exact plane476GenDeadBlock5
  | ⟨6, _⟩ => exact plane476GenDeadBlock6
  | ⟨7, _⟩ => exact plane476GenDeadBlock7
  | ⟨8, _⟩ => exact plane476GenDeadBlock8
  | ⟨9, _⟩ => exact plane476GenDeadBlock9
  | ⟨10, _⟩ => exact plane476GenDeadBlock10
  | ⟨11, _⟩ => exact plane476GenDeadBlock11
  | ⟨12, _⟩ => exact plane476GenDeadBlock12
  | ⟨13, _⟩ => exact plane476GenDeadBlock13
  | ⟨14, _⟩ => exact plane476GenDeadBlock14
  | ⟨15, _⟩ => exact plane476GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
