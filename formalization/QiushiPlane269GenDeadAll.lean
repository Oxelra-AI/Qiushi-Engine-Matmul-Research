import QiushiPlane269GenDeadBlock0
import QiushiPlane269GenDeadBlock1
import QiushiPlane269GenDeadBlock2
import QiushiPlane269GenDeadBlock3
import QiushiPlane269GenDeadBlock4
import QiushiPlane269GenDeadBlock5
import QiushiPlane269GenDeadBlock6
import QiushiPlane269GenDeadBlock7
import QiushiPlane269GenDeadBlock8
import QiushiPlane269GenDeadBlock9
import QiushiPlane269GenDeadBlock10
import QiushiPlane269GenDeadBlock11
import QiushiPlane269GenDeadBlock12
import QiushiPlane269GenDeadBlock13
import QiushiPlane269GenDeadBlock14
import QiushiPlane269GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane269GenDeadAll : forall i, plane269GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane269GenDeadBlock0
  | ⟨1, _⟩ => exact plane269GenDeadBlock1
  | ⟨2, _⟩ => exact plane269GenDeadBlock2
  | ⟨3, _⟩ => exact plane269GenDeadBlock3
  | ⟨4, _⟩ => exact plane269GenDeadBlock4
  | ⟨5, _⟩ => exact plane269GenDeadBlock5
  | ⟨6, _⟩ => exact plane269GenDeadBlock6
  | ⟨7, _⟩ => exact plane269GenDeadBlock7
  | ⟨8, _⟩ => exact plane269GenDeadBlock8
  | ⟨9, _⟩ => exact plane269GenDeadBlock9
  | ⟨10, _⟩ => exact plane269GenDeadBlock10
  | ⟨11, _⟩ => exact plane269GenDeadBlock11
  | ⟨12, _⟩ => exact plane269GenDeadBlock12
  | ⟨13, _⟩ => exact plane269GenDeadBlock13
  | ⟨14, _⟩ => exact plane269GenDeadBlock14
  | ⟨15, _⟩ => exact plane269GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
