import QiushiPlane471LowerGenDeadBlock0
import QiushiPlane471LowerGenDeadBlock1
import QiushiPlane471LowerGenDeadBlock2
import QiushiPlane471LowerGenDeadBlock3
import QiushiPlane471LowerGenDeadBlock4
import QiushiPlane471LowerGenDeadBlock5
import QiushiPlane471LowerGenDeadBlock6
import QiushiPlane471LowerGenDeadBlock7
import QiushiPlane471LowerGenDeadBlock8
import QiushiPlane471LowerGenDeadBlock9
import QiushiPlane471LowerGenDeadBlock10
import QiushiPlane471LowerGenDeadBlock11
import QiushiPlane471LowerGenDeadBlock12
import QiushiPlane471LowerGenDeadBlock13
import QiushiPlane471LowerGenDeadBlock14
import QiushiPlane471LowerGenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane471LowerGenDeadAll : forall i, plane471LowerGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane471LowerGenDeadBlock0
  | ⟨1, _⟩ => exact plane471LowerGenDeadBlock1
  | ⟨2, _⟩ => exact plane471LowerGenDeadBlock2
  | ⟨3, _⟩ => exact plane471LowerGenDeadBlock3
  | ⟨4, _⟩ => exact plane471LowerGenDeadBlock4
  | ⟨5, _⟩ => exact plane471LowerGenDeadBlock5
  | ⟨6, _⟩ => exact plane471LowerGenDeadBlock6
  | ⟨7, _⟩ => exact plane471LowerGenDeadBlock7
  | ⟨8, _⟩ => exact plane471LowerGenDeadBlock8
  | ⟨9, _⟩ => exact plane471LowerGenDeadBlock9
  | ⟨10, _⟩ => exact plane471LowerGenDeadBlock10
  | ⟨11, _⟩ => exact plane471LowerGenDeadBlock11
  | ⟨12, _⟩ => exact plane471LowerGenDeadBlock12
  | ⟨13, _⟩ => exact plane471LowerGenDeadBlock13
  | ⟨14, _⟩ => exact plane471LowerGenDeadBlock14
  | ⟨15, _⟩ => exact plane471LowerGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
