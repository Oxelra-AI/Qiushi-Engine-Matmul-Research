import QiushiPlane485GenSourceBlock0
import QiushiPlane485GenSourceBlock1
import QiushiPlane485GenSourceBlock2
import QiushiPlane485GenSourceBlock3
import QiushiPlane485GenSourceBlock4
import QiushiPlane485GenSourceBlock5
import QiushiPlane485GenSourceBlock6
import QiushiPlane485GenSourceBlock7
import QiushiPlane485GenSourceBlock8
import QiushiPlane485GenSourceBlock9
import QiushiPlane485GenSourceBlock10
import QiushiPlane485GenSourceBlock11
import QiushiPlane485GenSourceBlock12
import QiushiPlane485GenSourceBlock13
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane485GenSourceAll : forall i, plane485GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 14) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane485GenSourceBlock0
  | ⟨1, _⟩ => exact plane485GenSourceBlock1
  | ⟨2, _⟩ => exact plane485GenSourceBlock2
  | ⟨3, _⟩ => exact plane485GenSourceBlock3
  | ⟨4, _⟩ => exact plane485GenSourceBlock4
  | ⟨5, _⟩ => exact plane485GenSourceBlock5
  | ⟨6, _⟩ => exact plane485GenSourceBlock6
  | ⟨7, _⟩ => exact plane485GenSourceBlock7
  | ⟨8, _⟩ => exact plane485GenSourceBlock8
  | ⟨9, _⟩ => exact plane485GenSourceBlock9
  | ⟨10, _⟩ => exact plane485GenSourceBlock10
  | ⟨11, _⟩ => exact plane485GenSourceBlock11
  | ⟨12, _⟩ => exact plane485GenSourceBlock12
  | ⟨13, _⟩ => exact plane485GenSourceBlock13
  | ⟨k + 14, h⟩ => omega
end QiushiMatmul
