import QiushiPlane152GenDeadBlock0
import QiushiPlane152GenDeadBlock1
import QiushiPlane152GenDeadBlock2
import QiushiPlane152GenDeadBlock3
import QiushiPlane152GenDeadBlock4
import QiushiPlane152GenDeadBlock5
import QiushiPlane152GenDeadBlock6
import QiushiPlane152GenDeadBlock7
import QiushiPlane152GenDeadBlock8
import QiushiPlane152GenDeadBlock9
import QiushiPlane152GenDeadBlock10
import QiushiPlane152GenDeadBlock11
import QiushiPlane152GenDeadBlock12
import QiushiPlane152GenDeadBlock13
import QiushiPlane152GenDeadBlock14
import QiushiPlane152GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane152GenDeadAll : forall i, plane152GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane152GenDeadBlock0
  | ⟨1, _⟩ => exact plane152GenDeadBlock1
  | ⟨2, _⟩ => exact plane152GenDeadBlock2
  | ⟨3, _⟩ => exact plane152GenDeadBlock3
  | ⟨4, _⟩ => exact plane152GenDeadBlock4
  | ⟨5, _⟩ => exact plane152GenDeadBlock5
  | ⟨6, _⟩ => exact plane152GenDeadBlock6
  | ⟨7, _⟩ => exact plane152GenDeadBlock7
  | ⟨8, _⟩ => exact plane152GenDeadBlock8
  | ⟨9, _⟩ => exact plane152GenDeadBlock9
  | ⟨10, _⟩ => exact plane152GenDeadBlock10
  | ⟨11, _⟩ => exact plane152GenDeadBlock11
  | ⟨12, _⟩ => exact plane152GenDeadBlock12
  | ⟨13, _⟩ => exact plane152GenDeadBlock13
  | ⟨14, _⟩ => exact plane152GenDeadBlock14
  | ⟨15, _⟩ => exact plane152GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
