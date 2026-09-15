import QiushiPlane475GenDeadBlock0
import QiushiPlane475GenDeadBlock1
import QiushiPlane475GenDeadBlock2
import QiushiPlane475GenDeadBlock3
import QiushiPlane475GenDeadBlock4
import QiushiPlane475GenDeadBlock5
import QiushiPlane475GenDeadBlock6
import QiushiPlane475GenDeadBlock7
import QiushiPlane475GenDeadBlock8
import QiushiPlane475GenDeadBlock9
import QiushiPlane475GenDeadBlock10
import QiushiPlane475GenDeadBlock11
import QiushiPlane475GenDeadBlock12
import QiushiPlane475GenDeadBlock13
import QiushiPlane475GenDeadBlock14
import QiushiPlane475GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane475GenDeadAll : forall i, plane475GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane475GenDeadBlock0
  | ⟨1, _⟩ => exact plane475GenDeadBlock1
  | ⟨2, _⟩ => exact plane475GenDeadBlock2
  | ⟨3, _⟩ => exact plane475GenDeadBlock3
  | ⟨4, _⟩ => exact plane475GenDeadBlock4
  | ⟨5, _⟩ => exact plane475GenDeadBlock5
  | ⟨6, _⟩ => exact plane475GenDeadBlock6
  | ⟨7, _⟩ => exact plane475GenDeadBlock7
  | ⟨8, _⟩ => exact plane475GenDeadBlock8
  | ⟨9, _⟩ => exact plane475GenDeadBlock9
  | ⟨10, _⟩ => exact plane475GenDeadBlock10
  | ⟨11, _⟩ => exact plane475GenDeadBlock11
  | ⟨12, _⟩ => exact plane475GenDeadBlock12
  | ⟨13, _⟩ => exact plane475GenDeadBlock13
  | ⟨14, _⟩ => exact plane475GenDeadBlock14
  | ⟨15, _⟩ => exact plane475GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
