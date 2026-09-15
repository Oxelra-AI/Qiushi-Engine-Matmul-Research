import QiushiPlane274GenDeadBlock0
import QiushiPlane274GenDeadBlock1
import QiushiPlane274GenDeadBlock2
import QiushiPlane274GenDeadBlock3
import QiushiPlane274GenDeadBlock4
import QiushiPlane274GenDeadBlock5
import QiushiPlane274GenDeadBlock6
import QiushiPlane274GenDeadBlock7
import QiushiPlane274GenDeadBlock8
import QiushiPlane274GenDeadBlock9
import QiushiPlane274GenDeadBlock10
import QiushiPlane274GenDeadBlock11
import QiushiPlane274GenDeadBlock12
import QiushiPlane274GenDeadBlock13
import QiushiPlane274GenDeadBlock14
import QiushiPlane274GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane274GenDeadAll : forall i, plane274GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane274GenDeadBlock0
  | ⟨1, _⟩ => exact plane274GenDeadBlock1
  | ⟨2, _⟩ => exact plane274GenDeadBlock2
  | ⟨3, _⟩ => exact plane274GenDeadBlock3
  | ⟨4, _⟩ => exact plane274GenDeadBlock4
  | ⟨5, _⟩ => exact plane274GenDeadBlock5
  | ⟨6, _⟩ => exact plane274GenDeadBlock6
  | ⟨7, _⟩ => exact plane274GenDeadBlock7
  | ⟨8, _⟩ => exact plane274GenDeadBlock8
  | ⟨9, _⟩ => exact plane274GenDeadBlock9
  | ⟨10, _⟩ => exact plane274GenDeadBlock10
  | ⟨11, _⟩ => exact plane274GenDeadBlock11
  | ⟨12, _⟩ => exact plane274GenDeadBlock12
  | ⟨13, _⟩ => exact plane274GenDeadBlock13
  | ⟨14, _⟩ => exact plane274GenDeadBlock14
  | ⟨15, _⟩ => exact plane274GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
