import QiushiPlane470LowerGenDeadBlock0
import QiushiPlane470LowerGenDeadBlock1
import QiushiPlane470LowerGenDeadBlock2
import QiushiPlane470LowerGenDeadBlock3
import QiushiPlane470LowerGenDeadBlock4
import QiushiPlane470LowerGenDeadBlock5
import QiushiPlane470LowerGenDeadBlock6
import QiushiPlane470LowerGenDeadBlock7
import QiushiPlane470LowerGenDeadBlock8
import QiushiPlane470LowerGenDeadBlock9
import QiushiPlane470LowerGenDeadBlock10
import QiushiPlane470LowerGenDeadBlock11
import QiushiPlane470LowerGenDeadBlock12
import QiushiPlane470LowerGenDeadBlock13
import QiushiPlane470LowerGenDeadBlock14
import QiushiPlane470LowerGenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane470LowerGenDeadAll : forall i, plane470LowerGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane470LowerGenDeadBlock0
  | ⟨1, _⟩ => exact plane470LowerGenDeadBlock1
  | ⟨2, _⟩ => exact plane470LowerGenDeadBlock2
  | ⟨3, _⟩ => exact plane470LowerGenDeadBlock3
  | ⟨4, _⟩ => exact plane470LowerGenDeadBlock4
  | ⟨5, _⟩ => exact plane470LowerGenDeadBlock5
  | ⟨6, _⟩ => exact plane470LowerGenDeadBlock6
  | ⟨7, _⟩ => exact plane470LowerGenDeadBlock7
  | ⟨8, _⟩ => exact plane470LowerGenDeadBlock8
  | ⟨9, _⟩ => exact plane470LowerGenDeadBlock9
  | ⟨10, _⟩ => exact plane470LowerGenDeadBlock10
  | ⟨11, _⟩ => exact plane470LowerGenDeadBlock11
  | ⟨12, _⟩ => exact plane470LowerGenDeadBlock12
  | ⟨13, _⟩ => exact plane470LowerGenDeadBlock13
  | ⟨14, _⟩ => exact plane470LowerGenDeadBlock14
  | ⟨15, _⟩ => exact plane470LowerGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
