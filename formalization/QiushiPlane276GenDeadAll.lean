import QiushiPlane276GenDeadBlock0
import QiushiPlane276GenDeadBlock1
import QiushiPlane276GenDeadBlock2
import QiushiPlane276GenDeadBlock3
import QiushiPlane276GenDeadBlock4
import QiushiPlane276GenDeadBlock5
import QiushiPlane276GenDeadBlock6
import QiushiPlane276GenDeadBlock7
import QiushiPlane276GenDeadBlock8
import QiushiPlane276GenDeadBlock9
import QiushiPlane276GenDeadBlock10
import QiushiPlane276GenDeadBlock11
import QiushiPlane276GenDeadBlock12
import QiushiPlane276GenDeadBlock13
import QiushiPlane276GenDeadBlock14
import QiushiPlane276GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane276GenDeadAll : forall i, plane276GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane276GenDeadBlock0
  | ⟨1, _⟩ => exact plane276GenDeadBlock1
  | ⟨2, _⟩ => exact plane276GenDeadBlock2
  | ⟨3, _⟩ => exact plane276GenDeadBlock3
  | ⟨4, _⟩ => exact plane276GenDeadBlock4
  | ⟨5, _⟩ => exact plane276GenDeadBlock5
  | ⟨6, _⟩ => exact plane276GenDeadBlock6
  | ⟨7, _⟩ => exact plane276GenDeadBlock7
  | ⟨8, _⟩ => exact plane276GenDeadBlock8
  | ⟨9, _⟩ => exact plane276GenDeadBlock9
  | ⟨10, _⟩ => exact plane276GenDeadBlock10
  | ⟨11, _⟩ => exact plane276GenDeadBlock11
  | ⟨12, _⟩ => exact plane276GenDeadBlock12
  | ⟨13, _⟩ => exact plane276GenDeadBlock13
  | ⟨14, _⟩ => exact plane276GenDeadBlock14
  | ⟨15, _⟩ => exact plane276GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
