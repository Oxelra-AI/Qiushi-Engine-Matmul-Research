import QiushiPlane472GenSourceBlock0
import QiushiPlane472GenSourceBlock1
import QiushiPlane472GenSourceBlock2
import QiushiPlane472GenSourceBlock3
import QiushiPlane472GenSourceBlock4
import QiushiPlane472GenSourceBlock5
import QiushiPlane472GenSourceBlock6
import QiushiPlane472GenSourceBlock7
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane472GenSourceAll : forall i, plane472GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 8) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane472GenSourceBlock0
  | ⟨1, _⟩ => exact plane472GenSourceBlock1
  | ⟨2, _⟩ => exact plane472GenSourceBlock2
  | ⟨3, _⟩ => exact plane472GenSourceBlock3
  | ⟨4, _⟩ => exact plane472GenSourceBlock4
  | ⟨5, _⟩ => exact plane472GenSourceBlock5
  | ⟨6, _⟩ => exact plane472GenSourceBlock6
  | ⟨7, _⟩ => exact plane472GenSourceBlock7
  | ⟨k + 8, h⟩ => omega
end QiushiMatmul
