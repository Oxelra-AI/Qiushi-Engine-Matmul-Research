import QiushiPlane461GenDeadBlock0
import QiushiPlane461GenDeadBlock1
import QiushiPlane461GenDeadBlock2
import QiushiPlane461GenDeadBlock3
import QiushiPlane461GenDeadBlock4
import QiushiPlane461GenDeadBlock5
import QiushiPlane461GenDeadBlock6
import QiushiPlane461GenDeadBlock7
import QiushiPlane461GenDeadBlock8
import QiushiPlane461GenDeadBlock9
import QiushiPlane461GenDeadBlock10
import QiushiPlane461GenDeadBlock11
import QiushiPlane461GenDeadBlock12
import QiushiPlane461GenDeadBlock13
import QiushiPlane461GenDeadBlock14
import QiushiPlane461GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane461GenDeadAll : forall i, plane461GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane461GenDeadBlock0
  | ⟨1, _⟩ => exact plane461GenDeadBlock1
  | ⟨2, _⟩ => exact plane461GenDeadBlock2
  | ⟨3, _⟩ => exact plane461GenDeadBlock3
  | ⟨4, _⟩ => exact plane461GenDeadBlock4
  | ⟨5, _⟩ => exact plane461GenDeadBlock5
  | ⟨6, _⟩ => exact plane461GenDeadBlock6
  | ⟨7, _⟩ => exact plane461GenDeadBlock7
  | ⟨8, _⟩ => exact plane461GenDeadBlock8
  | ⟨9, _⟩ => exact plane461GenDeadBlock9
  | ⟨10, _⟩ => exact plane461GenDeadBlock10
  | ⟨11, _⟩ => exact plane461GenDeadBlock11
  | ⟨12, _⟩ => exact plane461GenDeadBlock12
  | ⟨13, _⟩ => exact plane461GenDeadBlock13
  | ⟨14, _⟩ => exact plane461GenDeadBlock14
  | ⟨15, _⟩ => exact plane461GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
