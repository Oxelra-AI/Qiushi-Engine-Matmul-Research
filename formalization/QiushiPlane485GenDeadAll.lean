import QiushiPlane485GenDeadBlock0
import QiushiPlane485GenDeadBlock1
import QiushiPlane485GenDeadBlock2
import QiushiPlane485GenDeadBlock3
import QiushiPlane485GenDeadBlock4
import QiushiPlane485GenDeadBlock5
import QiushiPlane485GenDeadBlock6
import QiushiPlane485GenDeadBlock7
import QiushiPlane485GenDeadBlock8
import QiushiPlane485GenDeadBlock9
import QiushiPlane485GenDeadBlock10
import QiushiPlane485GenDeadBlock11
import QiushiPlane485GenDeadBlock12
import QiushiPlane485GenDeadBlock13
import QiushiPlane485GenDeadBlock14
import QiushiPlane485GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane485GenDeadAll : forall i, plane485GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane485GenDeadBlock0
  | ⟨1, _⟩ => exact plane485GenDeadBlock1
  | ⟨2, _⟩ => exact plane485GenDeadBlock2
  | ⟨3, _⟩ => exact plane485GenDeadBlock3
  | ⟨4, _⟩ => exact plane485GenDeadBlock4
  | ⟨5, _⟩ => exact plane485GenDeadBlock5
  | ⟨6, _⟩ => exact plane485GenDeadBlock6
  | ⟨7, _⟩ => exact plane485GenDeadBlock7
  | ⟨8, _⟩ => exact plane485GenDeadBlock8
  | ⟨9, _⟩ => exact plane485GenDeadBlock9
  | ⟨10, _⟩ => exact plane485GenDeadBlock10
  | ⟨11, _⟩ => exact plane485GenDeadBlock11
  | ⟨12, _⟩ => exact plane485GenDeadBlock12
  | ⟨13, _⟩ => exact plane485GenDeadBlock13
  | ⟨14, _⟩ => exact plane485GenDeadBlock14
  | ⟨15, _⟩ => exact plane485GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
