import QiushiPlane463LowerGenDeadBlock0
import QiushiPlane463LowerGenDeadBlock1
import QiushiPlane463LowerGenDeadBlock2
import QiushiPlane463LowerGenDeadBlock3
import QiushiPlane463LowerGenDeadBlock4
import QiushiPlane463LowerGenDeadBlock5
import QiushiPlane463LowerGenDeadBlock6
import QiushiPlane463LowerGenDeadBlock7
import QiushiPlane463LowerGenDeadBlock8
import QiushiPlane463LowerGenDeadBlock9
import QiushiPlane463LowerGenDeadBlock10
import QiushiPlane463LowerGenDeadBlock11
import QiushiPlane463LowerGenDeadBlock12
import QiushiPlane463LowerGenDeadBlock13
import QiushiPlane463LowerGenDeadBlock14
import QiushiPlane463LowerGenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane463LowerGenDeadAll : forall i, plane463LowerGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane463LowerGenDeadBlock0
  | ⟨1, _⟩ => exact plane463LowerGenDeadBlock1
  | ⟨2, _⟩ => exact plane463LowerGenDeadBlock2
  | ⟨3, _⟩ => exact plane463LowerGenDeadBlock3
  | ⟨4, _⟩ => exact plane463LowerGenDeadBlock4
  | ⟨5, _⟩ => exact plane463LowerGenDeadBlock5
  | ⟨6, _⟩ => exact plane463LowerGenDeadBlock6
  | ⟨7, _⟩ => exact plane463LowerGenDeadBlock7
  | ⟨8, _⟩ => exact plane463LowerGenDeadBlock8
  | ⟨9, _⟩ => exact plane463LowerGenDeadBlock9
  | ⟨10, _⟩ => exact plane463LowerGenDeadBlock10
  | ⟨11, _⟩ => exact plane463LowerGenDeadBlock11
  | ⟨12, _⟩ => exact plane463LowerGenDeadBlock12
  | ⟨13, _⟩ => exact plane463LowerGenDeadBlock13
  | ⟨14, _⟩ => exact plane463LowerGenDeadBlock14
  | ⟨15, _⟩ => exact plane463LowerGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
