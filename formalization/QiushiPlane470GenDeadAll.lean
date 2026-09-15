import QiushiPlane470GenDeadBlock0
import QiushiPlane470GenDeadBlock1
import QiushiPlane470GenDeadBlock2
import QiushiPlane470GenDeadBlock3
import QiushiPlane470GenDeadBlock4
import QiushiPlane470GenDeadBlock5
import QiushiPlane470GenDeadBlock6
import QiushiPlane470GenDeadBlock7
import QiushiPlane470GenDeadBlock8
import QiushiPlane470GenDeadBlock9
import QiushiPlane470GenDeadBlock10
import QiushiPlane470GenDeadBlock11
import QiushiPlane470GenDeadBlock12
import QiushiPlane470GenDeadBlock13
import QiushiPlane470GenDeadBlock14
import QiushiPlane470GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane470GenDeadAll : forall i, plane470GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane470GenDeadBlock0
  | ⟨1, _⟩ => exact plane470GenDeadBlock1
  | ⟨2, _⟩ => exact plane470GenDeadBlock2
  | ⟨3, _⟩ => exact plane470GenDeadBlock3
  | ⟨4, _⟩ => exact plane470GenDeadBlock4
  | ⟨5, _⟩ => exact plane470GenDeadBlock5
  | ⟨6, _⟩ => exact plane470GenDeadBlock6
  | ⟨7, _⟩ => exact plane470GenDeadBlock7
  | ⟨8, _⟩ => exact plane470GenDeadBlock8
  | ⟨9, _⟩ => exact plane470GenDeadBlock9
  | ⟨10, _⟩ => exact plane470GenDeadBlock10
  | ⟨11, _⟩ => exact plane470GenDeadBlock11
  | ⟨12, _⟩ => exact plane470GenDeadBlock12
  | ⟨13, _⟩ => exact plane470GenDeadBlock13
  | ⟨14, _⟩ => exact plane470GenDeadBlock14
  | ⟨15, _⟩ => exact plane470GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
