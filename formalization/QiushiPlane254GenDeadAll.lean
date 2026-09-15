import QiushiPlane254GenDeadBlock0
import QiushiPlane254GenDeadBlock1
import QiushiPlane254GenDeadBlock2
import QiushiPlane254GenDeadBlock3
import QiushiPlane254GenDeadBlock4
import QiushiPlane254GenDeadBlock5
import QiushiPlane254GenDeadBlock6
import QiushiPlane254GenDeadBlock7
import QiushiPlane254GenDeadBlock8
import QiushiPlane254GenDeadBlock9
import QiushiPlane254GenDeadBlock10
import QiushiPlane254GenDeadBlock11
import QiushiPlane254GenDeadBlock12
import QiushiPlane254GenDeadBlock13
import QiushiPlane254GenDeadBlock14
import QiushiPlane254GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane254GenDeadAll : forall i, plane254GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane254GenDeadBlock0
  | ⟨1, _⟩ => exact plane254GenDeadBlock1
  | ⟨2, _⟩ => exact plane254GenDeadBlock2
  | ⟨3, _⟩ => exact plane254GenDeadBlock3
  | ⟨4, _⟩ => exact plane254GenDeadBlock4
  | ⟨5, _⟩ => exact plane254GenDeadBlock5
  | ⟨6, _⟩ => exact plane254GenDeadBlock6
  | ⟨7, _⟩ => exact plane254GenDeadBlock7
  | ⟨8, _⟩ => exact plane254GenDeadBlock8
  | ⟨9, _⟩ => exact plane254GenDeadBlock9
  | ⟨10, _⟩ => exact plane254GenDeadBlock10
  | ⟨11, _⟩ => exact plane254GenDeadBlock11
  | ⟨12, _⟩ => exact plane254GenDeadBlock12
  | ⟨13, _⟩ => exact plane254GenDeadBlock13
  | ⟨14, _⟩ => exact plane254GenDeadBlock14
  | ⟨15, _⟩ => exact plane254GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
