import QiushiPlane448GenDeadBlock0
import QiushiPlane448GenDeadBlock1
import QiushiPlane448GenDeadBlock2
import QiushiPlane448GenDeadBlock3
import QiushiPlane448GenDeadBlock4
import QiushiPlane448GenDeadBlock5
import QiushiPlane448GenDeadBlock6
import QiushiPlane448GenDeadBlock7
import QiushiPlane448GenDeadBlock8
import QiushiPlane448GenDeadBlock9
import QiushiPlane448GenDeadBlock10
import QiushiPlane448GenDeadBlock11
import QiushiPlane448GenDeadBlock12
import QiushiPlane448GenDeadBlock13
import QiushiPlane448GenDeadBlock14
import QiushiPlane448GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane448GenDeadAll : forall i, plane448GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane448GenDeadBlock0
  | ⟨1, _⟩ => exact plane448GenDeadBlock1
  | ⟨2, _⟩ => exact plane448GenDeadBlock2
  | ⟨3, _⟩ => exact plane448GenDeadBlock3
  | ⟨4, _⟩ => exact plane448GenDeadBlock4
  | ⟨5, _⟩ => exact plane448GenDeadBlock5
  | ⟨6, _⟩ => exact plane448GenDeadBlock6
  | ⟨7, _⟩ => exact plane448GenDeadBlock7
  | ⟨8, _⟩ => exact plane448GenDeadBlock8
  | ⟨9, _⟩ => exact plane448GenDeadBlock9
  | ⟨10, _⟩ => exact plane448GenDeadBlock10
  | ⟨11, _⟩ => exact plane448GenDeadBlock11
  | ⟨12, _⟩ => exact plane448GenDeadBlock12
  | ⟨13, _⟩ => exact plane448GenDeadBlock13
  | ⟨14, _⟩ => exact plane448GenDeadBlock14
  | ⟨15, _⟩ => exact plane448GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
