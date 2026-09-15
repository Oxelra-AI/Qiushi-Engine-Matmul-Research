import QiushiPlane463GenDeadBlock0
import QiushiPlane463GenDeadBlock1
import QiushiPlane463GenDeadBlock2
import QiushiPlane463GenDeadBlock3
import QiushiPlane463GenDeadBlock4
import QiushiPlane463GenDeadBlock5
import QiushiPlane463GenDeadBlock6
import QiushiPlane463GenDeadBlock7
import QiushiPlane463GenDeadBlock8
import QiushiPlane463GenDeadBlock9
import QiushiPlane463GenDeadBlock10
import QiushiPlane463GenDeadBlock11
import QiushiPlane463GenDeadBlock12
import QiushiPlane463GenDeadBlock13
import QiushiPlane463GenDeadBlock14
import QiushiPlane463GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane463GenDeadAll : forall i, plane463GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane463GenDeadBlock0
  | ⟨1, _⟩ => exact plane463GenDeadBlock1
  | ⟨2, _⟩ => exact plane463GenDeadBlock2
  | ⟨3, _⟩ => exact plane463GenDeadBlock3
  | ⟨4, _⟩ => exact plane463GenDeadBlock4
  | ⟨5, _⟩ => exact plane463GenDeadBlock5
  | ⟨6, _⟩ => exact plane463GenDeadBlock6
  | ⟨7, _⟩ => exact plane463GenDeadBlock7
  | ⟨8, _⟩ => exact plane463GenDeadBlock8
  | ⟨9, _⟩ => exact plane463GenDeadBlock9
  | ⟨10, _⟩ => exact plane463GenDeadBlock10
  | ⟨11, _⟩ => exact plane463GenDeadBlock11
  | ⟨12, _⟩ => exact plane463GenDeadBlock12
  | ⟨13, _⟩ => exact plane463GenDeadBlock13
  | ⟨14, _⟩ => exact plane463GenDeadBlock14
  | ⟨15, _⟩ => exact plane463GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
