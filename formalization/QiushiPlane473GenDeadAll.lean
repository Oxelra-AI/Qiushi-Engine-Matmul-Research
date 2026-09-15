import QiushiPlane473GenDeadBlock0
import QiushiPlane473GenDeadBlock1
import QiushiPlane473GenDeadBlock2
import QiushiPlane473GenDeadBlock3
import QiushiPlane473GenDeadBlock4
import QiushiPlane473GenDeadBlock5
import QiushiPlane473GenDeadBlock6
import QiushiPlane473GenDeadBlock7
import QiushiPlane473GenDeadBlock8
import QiushiPlane473GenDeadBlock9
import QiushiPlane473GenDeadBlock10
import QiushiPlane473GenDeadBlock11
import QiushiPlane473GenDeadBlock12
import QiushiPlane473GenDeadBlock13
import QiushiPlane473GenDeadBlock14
import QiushiPlane473GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane473GenDeadAll : forall i, plane473GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane473GenDeadBlock0
  | ⟨1, _⟩ => exact plane473GenDeadBlock1
  | ⟨2, _⟩ => exact plane473GenDeadBlock2
  | ⟨3, _⟩ => exact plane473GenDeadBlock3
  | ⟨4, _⟩ => exact plane473GenDeadBlock4
  | ⟨5, _⟩ => exact plane473GenDeadBlock5
  | ⟨6, _⟩ => exact plane473GenDeadBlock6
  | ⟨7, _⟩ => exact plane473GenDeadBlock7
  | ⟨8, _⟩ => exact plane473GenDeadBlock8
  | ⟨9, _⟩ => exact plane473GenDeadBlock9
  | ⟨10, _⟩ => exact plane473GenDeadBlock10
  | ⟨11, _⟩ => exact plane473GenDeadBlock11
  | ⟨12, _⟩ => exact plane473GenDeadBlock12
  | ⟨13, _⟩ => exact plane473GenDeadBlock13
  | ⟨14, _⟩ => exact plane473GenDeadBlock14
  | ⟨15, _⟩ => exact plane473GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
