import QiushiPlane454GenDeadBlock0
import QiushiPlane454GenDeadBlock1
import QiushiPlane454GenDeadBlock2
import QiushiPlane454GenDeadBlock3
import QiushiPlane454GenDeadBlock4
import QiushiPlane454GenDeadBlock5
import QiushiPlane454GenDeadBlock6
import QiushiPlane454GenDeadBlock7
import QiushiPlane454GenDeadBlock8
import QiushiPlane454GenDeadBlock9
import QiushiPlane454GenDeadBlock10
import QiushiPlane454GenDeadBlock11
import QiushiPlane454GenDeadBlock12
import QiushiPlane454GenDeadBlock13
import QiushiPlane454GenDeadBlock14
import QiushiPlane454GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane454GenDeadAll : forall i, plane454GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane454GenDeadBlock0
  | ⟨1, _⟩ => exact plane454GenDeadBlock1
  | ⟨2, _⟩ => exact plane454GenDeadBlock2
  | ⟨3, _⟩ => exact plane454GenDeadBlock3
  | ⟨4, _⟩ => exact plane454GenDeadBlock4
  | ⟨5, _⟩ => exact plane454GenDeadBlock5
  | ⟨6, _⟩ => exact plane454GenDeadBlock6
  | ⟨7, _⟩ => exact plane454GenDeadBlock7
  | ⟨8, _⟩ => exact plane454GenDeadBlock8
  | ⟨9, _⟩ => exact plane454GenDeadBlock9
  | ⟨10, _⟩ => exact plane454GenDeadBlock10
  | ⟨11, _⟩ => exact plane454GenDeadBlock11
  | ⟨12, _⟩ => exact plane454GenDeadBlock12
  | ⟨13, _⟩ => exact plane454GenDeadBlock13
  | ⟨14, _⟩ => exact plane454GenDeadBlock14
  | ⟨15, _⟩ => exact plane454GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
