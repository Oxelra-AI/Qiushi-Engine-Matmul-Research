import QiushiPlane413GenDeadBlock0
import QiushiPlane413GenDeadBlock1
import QiushiPlane413GenDeadBlock2
import QiushiPlane413GenDeadBlock3
import QiushiPlane413GenDeadBlock4
import QiushiPlane413GenDeadBlock5
import QiushiPlane413GenDeadBlock6
import QiushiPlane413GenDeadBlock7
import QiushiPlane413GenDeadBlock8
import QiushiPlane413GenDeadBlock9
import QiushiPlane413GenDeadBlock10
import QiushiPlane413GenDeadBlock11
import QiushiPlane413GenDeadBlock12
import QiushiPlane413GenDeadBlock13
import QiushiPlane413GenDeadBlock14
import QiushiPlane413GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane413GenDeadAll : forall i, plane413GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane413GenDeadBlock0
  | ⟨1, _⟩ => exact plane413GenDeadBlock1
  | ⟨2, _⟩ => exact plane413GenDeadBlock2
  | ⟨3, _⟩ => exact plane413GenDeadBlock3
  | ⟨4, _⟩ => exact plane413GenDeadBlock4
  | ⟨5, _⟩ => exact plane413GenDeadBlock5
  | ⟨6, _⟩ => exact plane413GenDeadBlock6
  | ⟨7, _⟩ => exact plane413GenDeadBlock7
  | ⟨8, _⟩ => exact plane413GenDeadBlock8
  | ⟨9, _⟩ => exact plane413GenDeadBlock9
  | ⟨10, _⟩ => exact plane413GenDeadBlock10
  | ⟨11, _⟩ => exact plane413GenDeadBlock11
  | ⟨12, _⟩ => exact plane413GenDeadBlock12
  | ⟨13, _⟩ => exact plane413GenDeadBlock13
  | ⟨14, _⟩ => exact plane413GenDeadBlock14
  | ⟨15, _⟩ => exact plane413GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
