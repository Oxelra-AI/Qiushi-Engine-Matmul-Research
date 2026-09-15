import QiushiPlane275GenDeadBlock0
import QiushiPlane275GenDeadBlock1
import QiushiPlane275GenDeadBlock2
import QiushiPlane275GenDeadBlock3
import QiushiPlane275GenDeadBlock4
import QiushiPlane275GenDeadBlock5
import QiushiPlane275GenDeadBlock6
import QiushiPlane275GenDeadBlock7
import QiushiPlane275GenDeadBlock8
import QiushiPlane275GenDeadBlock9
import QiushiPlane275GenDeadBlock10
import QiushiPlane275GenDeadBlock11
import QiushiPlane275GenDeadBlock12
import QiushiPlane275GenDeadBlock13
import QiushiPlane275GenDeadBlock14
import QiushiPlane275GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane275GenDeadAll : forall i, plane275GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane275GenDeadBlock0
  | ⟨1, _⟩ => exact plane275GenDeadBlock1
  | ⟨2, _⟩ => exact plane275GenDeadBlock2
  | ⟨3, _⟩ => exact plane275GenDeadBlock3
  | ⟨4, _⟩ => exact plane275GenDeadBlock4
  | ⟨5, _⟩ => exact plane275GenDeadBlock5
  | ⟨6, _⟩ => exact plane275GenDeadBlock6
  | ⟨7, _⟩ => exact plane275GenDeadBlock7
  | ⟨8, _⟩ => exact plane275GenDeadBlock8
  | ⟨9, _⟩ => exact plane275GenDeadBlock9
  | ⟨10, _⟩ => exact plane275GenDeadBlock10
  | ⟨11, _⟩ => exact plane275GenDeadBlock11
  | ⟨12, _⟩ => exact plane275GenDeadBlock12
  | ⟨13, _⟩ => exact plane275GenDeadBlock13
  | ⟨14, _⟩ => exact plane275GenDeadBlock14
  | ⟨15, _⟩ => exact plane275GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
