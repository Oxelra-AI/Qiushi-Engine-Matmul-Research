import QiushiPlane427GenDeadBlock0
import QiushiPlane427GenDeadBlock1
import QiushiPlane427GenDeadBlock2
import QiushiPlane427GenDeadBlock3
import QiushiPlane427GenDeadBlock4
import QiushiPlane427GenDeadBlock5
import QiushiPlane427GenDeadBlock6
import QiushiPlane427GenDeadBlock7
import QiushiPlane427GenDeadBlock8
import QiushiPlane427GenDeadBlock9
import QiushiPlane427GenDeadBlock10
import QiushiPlane427GenDeadBlock11
import QiushiPlane427GenDeadBlock12
import QiushiPlane427GenDeadBlock13
import QiushiPlane427GenDeadBlock14
import QiushiPlane427GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane427GenDeadAll : forall i, plane427GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane427GenDeadBlock0
  | ⟨1, _⟩ => exact plane427GenDeadBlock1
  | ⟨2, _⟩ => exact plane427GenDeadBlock2
  | ⟨3, _⟩ => exact plane427GenDeadBlock3
  | ⟨4, _⟩ => exact plane427GenDeadBlock4
  | ⟨5, _⟩ => exact plane427GenDeadBlock5
  | ⟨6, _⟩ => exact plane427GenDeadBlock6
  | ⟨7, _⟩ => exact plane427GenDeadBlock7
  | ⟨8, _⟩ => exact plane427GenDeadBlock8
  | ⟨9, _⟩ => exact plane427GenDeadBlock9
  | ⟨10, _⟩ => exact plane427GenDeadBlock10
  | ⟨11, _⟩ => exact plane427GenDeadBlock11
  | ⟨12, _⟩ => exact plane427GenDeadBlock12
  | ⟨13, _⟩ => exact plane427GenDeadBlock13
  | ⟨14, _⟩ => exact plane427GenDeadBlock14
  | ⟨15, _⟩ => exact plane427GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
