import QiushiPlane472GenIndicatorBlock0
import QiushiPlane472GenIndicatorBlock1
import QiushiPlane472GenIndicatorBlock2
import QiushiPlane472GenIndicatorBlock3
import QiushiPlane472GenIndicatorBlock4
import QiushiPlane472GenIndicatorBlock5
import QiushiPlane472GenIndicatorBlock6
import QiushiPlane472GenIndicatorBlock7
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane472GenIndicatorAll : forall i, plane472GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 8) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane472GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane472GenIndicatorBlock1
  | ⟨2, _⟩ => exact plane472GenIndicatorBlock2
  | ⟨3, _⟩ => exact plane472GenIndicatorBlock3
  | ⟨4, _⟩ => exact plane472GenIndicatorBlock4
  | ⟨5, _⟩ => exact plane472GenIndicatorBlock5
  | ⟨6, _⟩ => exact plane472GenIndicatorBlock6
  | ⟨7, _⟩ => exact plane472GenIndicatorBlock7
  | ⟨k + 8, h⟩ => omega
end QiushiMatmul
