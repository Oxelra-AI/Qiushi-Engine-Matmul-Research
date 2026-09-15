import QiushiPlane453GenDeadBlock0
import QiushiPlane453GenDeadBlock1
import QiushiPlane453GenDeadBlock2
import QiushiPlane453GenDeadBlock3
import QiushiPlane453GenDeadBlock4
import QiushiPlane453GenDeadBlock5
import QiushiPlane453GenDeadBlock6
import QiushiPlane453GenDeadBlock7
import QiushiPlane453GenDeadBlock8
import QiushiPlane453GenDeadBlock9
import QiushiPlane453GenDeadBlock10
import QiushiPlane453GenDeadBlock11
import QiushiPlane453GenDeadBlock12
import QiushiPlane453GenDeadBlock13
import QiushiPlane453GenDeadBlock14
import QiushiPlane453GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane453GenDeadAll : forall i, plane453GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane453GenDeadBlock0
  | ⟨1, _⟩ => exact plane453GenDeadBlock1
  | ⟨2, _⟩ => exact plane453GenDeadBlock2
  | ⟨3, _⟩ => exact plane453GenDeadBlock3
  | ⟨4, _⟩ => exact plane453GenDeadBlock4
  | ⟨5, _⟩ => exact plane453GenDeadBlock5
  | ⟨6, _⟩ => exact plane453GenDeadBlock6
  | ⟨7, _⟩ => exact plane453GenDeadBlock7
  | ⟨8, _⟩ => exact plane453GenDeadBlock8
  | ⟨9, _⟩ => exact plane453GenDeadBlock9
  | ⟨10, _⟩ => exact plane453GenDeadBlock10
  | ⟨11, _⟩ => exact plane453GenDeadBlock11
  | ⟨12, _⟩ => exact plane453GenDeadBlock12
  | ⟨13, _⟩ => exact plane453GenDeadBlock13
  | ⟨14, _⟩ => exact plane453GenDeadBlock14
  | ⟨15, _⟩ => exact plane453GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
