import QiushiPlane455GenDeadBlock0
import QiushiPlane455GenDeadBlock1
import QiushiPlane455GenDeadBlock2
import QiushiPlane455GenDeadBlock3
import QiushiPlane455GenDeadBlock4
import QiushiPlane455GenDeadBlock5
import QiushiPlane455GenDeadBlock6
import QiushiPlane455GenDeadBlock7
import QiushiPlane455GenDeadBlock8
import QiushiPlane455GenDeadBlock9
import QiushiPlane455GenDeadBlock10
import QiushiPlane455GenDeadBlock11
import QiushiPlane455GenDeadBlock12
import QiushiPlane455GenDeadBlock13
import QiushiPlane455GenDeadBlock14
import QiushiPlane455GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane455GenDeadAll : forall i, plane455GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane455GenDeadBlock0
  | ⟨1, _⟩ => exact plane455GenDeadBlock1
  | ⟨2, _⟩ => exact plane455GenDeadBlock2
  | ⟨3, _⟩ => exact plane455GenDeadBlock3
  | ⟨4, _⟩ => exact plane455GenDeadBlock4
  | ⟨5, _⟩ => exact plane455GenDeadBlock5
  | ⟨6, _⟩ => exact plane455GenDeadBlock6
  | ⟨7, _⟩ => exact plane455GenDeadBlock7
  | ⟨8, _⟩ => exact plane455GenDeadBlock8
  | ⟨9, _⟩ => exact plane455GenDeadBlock9
  | ⟨10, _⟩ => exact plane455GenDeadBlock10
  | ⟨11, _⟩ => exact plane455GenDeadBlock11
  | ⟨12, _⟩ => exact plane455GenDeadBlock12
  | ⟨13, _⟩ => exact plane455GenDeadBlock13
  | ⟨14, _⟩ => exact plane455GenDeadBlock14
  | ⟨15, _⟩ => exact plane455GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
