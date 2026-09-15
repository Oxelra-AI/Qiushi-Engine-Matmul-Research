import QiushiPlane292GenDeadBlock0
import QiushiPlane292GenDeadBlock1
import QiushiPlane292GenDeadBlock2
import QiushiPlane292GenDeadBlock3
import QiushiPlane292GenDeadBlock4
import QiushiPlane292GenDeadBlock5
import QiushiPlane292GenDeadBlock6
import QiushiPlane292GenDeadBlock7
import QiushiPlane292GenDeadBlock8
import QiushiPlane292GenDeadBlock9
import QiushiPlane292GenDeadBlock10
import QiushiPlane292GenDeadBlock11
import QiushiPlane292GenDeadBlock12
import QiushiPlane292GenDeadBlock13
import QiushiPlane292GenDeadBlock14
import QiushiPlane292GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane292GenDeadAll : forall i, plane292GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane292GenDeadBlock0
  | ⟨1, _⟩ => exact plane292GenDeadBlock1
  | ⟨2, _⟩ => exact plane292GenDeadBlock2
  | ⟨3, _⟩ => exact plane292GenDeadBlock3
  | ⟨4, _⟩ => exact plane292GenDeadBlock4
  | ⟨5, _⟩ => exact plane292GenDeadBlock5
  | ⟨6, _⟩ => exact plane292GenDeadBlock6
  | ⟨7, _⟩ => exact plane292GenDeadBlock7
  | ⟨8, _⟩ => exact plane292GenDeadBlock8
  | ⟨9, _⟩ => exact plane292GenDeadBlock9
  | ⟨10, _⟩ => exact plane292GenDeadBlock10
  | ⟨11, _⟩ => exact plane292GenDeadBlock11
  | ⟨12, _⟩ => exact plane292GenDeadBlock12
  | ⟨13, _⟩ => exact plane292GenDeadBlock13
  | ⟨14, _⟩ => exact plane292GenDeadBlock14
  | ⟨15, _⟩ => exact plane292GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
