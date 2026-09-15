import QiushiPlane298GenDeadBlock0
import QiushiPlane298GenDeadBlock1
import QiushiPlane298GenDeadBlock2
import QiushiPlane298GenDeadBlock3
import QiushiPlane298GenDeadBlock4
import QiushiPlane298GenDeadBlock5
import QiushiPlane298GenDeadBlock6
import QiushiPlane298GenDeadBlock7
import QiushiPlane298GenDeadBlock8
import QiushiPlane298GenDeadBlock9
import QiushiPlane298GenDeadBlock10
import QiushiPlane298GenDeadBlock11
import QiushiPlane298GenDeadBlock12
import QiushiPlane298GenDeadBlock13
import QiushiPlane298GenDeadBlock14
import QiushiPlane298GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane298GenDeadAll : forall i, plane298GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane298GenDeadBlock0
  | ⟨1, _⟩ => exact plane298GenDeadBlock1
  | ⟨2, _⟩ => exact plane298GenDeadBlock2
  | ⟨3, _⟩ => exact plane298GenDeadBlock3
  | ⟨4, _⟩ => exact plane298GenDeadBlock4
  | ⟨5, _⟩ => exact plane298GenDeadBlock5
  | ⟨6, _⟩ => exact plane298GenDeadBlock6
  | ⟨7, _⟩ => exact plane298GenDeadBlock7
  | ⟨8, _⟩ => exact plane298GenDeadBlock8
  | ⟨9, _⟩ => exact plane298GenDeadBlock9
  | ⟨10, _⟩ => exact plane298GenDeadBlock10
  | ⟨11, _⟩ => exact plane298GenDeadBlock11
  | ⟨12, _⟩ => exact plane298GenDeadBlock12
  | ⟨13, _⟩ => exact plane298GenDeadBlock13
  | ⟨14, _⟩ => exact plane298GenDeadBlock14
  | ⟨15, _⟩ => exact plane298GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
