import QiushiPlane465GenDeadBlock0
import QiushiPlane465GenDeadBlock1
import QiushiPlane465GenDeadBlock2
import QiushiPlane465GenDeadBlock3
import QiushiPlane465GenDeadBlock4
import QiushiPlane465GenDeadBlock5
import QiushiPlane465GenDeadBlock6
import QiushiPlane465GenDeadBlock7
import QiushiPlane465GenDeadBlock8
import QiushiPlane465GenDeadBlock9
import QiushiPlane465GenDeadBlock10
import QiushiPlane465GenDeadBlock11
import QiushiPlane465GenDeadBlock12
import QiushiPlane465GenDeadBlock13
import QiushiPlane465GenDeadBlock14
import QiushiPlane465GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane465GenDeadAll : forall i, plane465GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane465GenDeadBlock0
  | ⟨1, _⟩ => exact plane465GenDeadBlock1
  | ⟨2, _⟩ => exact plane465GenDeadBlock2
  | ⟨3, _⟩ => exact plane465GenDeadBlock3
  | ⟨4, _⟩ => exact plane465GenDeadBlock4
  | ⟨5, _⟩ => exact plane465GenDeadBlock5
  | ⟨6, _⟩ => exact plane465GenDeadBlock6
  | ⟨7, _⟩ => exact plane465GenDeadBlock7
  | ⟨8, _⟩ => exact plane465GenDeadBlock8
  | ⟨9, _⟩ => exact plane465GenDeadBlock9
  | ⟨10, _⟩ => exact plane465GenDeadBlock10
  | ⟨11, _⟩ => exact plane465GenDeadBlock11
  | ⟨12, _⟩ => exact plane465GenDeadBlock12
  | ⟨13, _⟩ => exact plane465GenDeadBlock13
  | ⟨14, _⟩ => exact plane465GenDeadBlock14
  | ⟨15, _⟩ => exact plane465GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
