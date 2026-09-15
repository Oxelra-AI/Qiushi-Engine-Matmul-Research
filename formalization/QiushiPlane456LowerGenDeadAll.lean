import QiushiPlane456LowerGenDeadBlock0
import QiushiPlane456LowerGenDeadBlock1
import QiushiPlane456LowerGenDeadBlock2
import QiushiPlane456LowerGenDeadBlock3
import QiushiPlane456LowerGenDeadBlock4
import QiushiPlane456LowerGenDeadBlock5
import QiushiPlane456LowerGenDeadBlock6
import QiushiPlane456LowerGenDeadBlock7
import QiushiPlane456LowerGenDeadBlock8
import QiushiPlane456LowerGenDeadBlock9
import QiushiPlane456LowerGenDeadBlock10
import QiushiPlane456LowerGenDeadBlock11
import QiushiPlane456LowerGenDeadBlock12
import QiushiPlane456LowerGenDeadBlock13
import QiushiPlane456LowerGenDeadBlock14
import QiushiPlane456LowerGenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane456LowerGenDeadAll : forall i, plane456LowerGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane456LowerGenDeadBlock0
  | ⟨1, _⟩ => exact plane456LowerGenDeadBlock1
  | ⟨2, _⟩ => exact plane456LowerGenDeadBlock2
  | ⟨3, _⟩ => exact plane456LowerGenDeadBlock3
  | ⟨4, _⟩ => exact plane456LowerGenDeadBlock4
  | ⟨5, _⟩ => exact plane456LowerGenDeadBlock5
  | ⟨6, _⟩ => exact plane456LowerGenDeadBlock6
  | ⟨7, _⟩ => exact plane456LowerGenDeadBlock7
  | ⟨8, _⟩ => exact plane456LowerGenDeadBlock8
  | ⟨9, _⟩ => exact plane456LowerGenDeadBlock9
  | ⟨10, _⟩ => exact plane456LowerGenDeadBlock10
  | ⟨11, _⟩ => exact plane456LowerGenDeadBlock11
  | ⟨12, _⟩ => exact plane456LowerGenDeadBlock12
  | ⟨13, _⟩ => exact plane456LowerGenDeadBlock13
  | ⟨14, _⟩ => exact plane456LowerGenDeadBlock14
  | ⟨15, _⟩ => exact plane456LowerGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
