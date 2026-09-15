import QiushiPlane457GenIndicatorBlock0
import QiushiPlane457GenIndicatorBlock1
import QiushiPlane457GenIndicatorBlock2
import QiushiPlane457GenIndicatorBlock3
import QiushiPlane457GenIndicatorBlock4
import QiushiPlane457GenIndicatorBlock5
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane457GenIndicatorAll : forall i, plane457GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 6) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane457GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane457GenIndicatorBlock1
  | ⟨2, _⟩ => exact plane457GenIndicatorBlock2
  | ⟨3, _⟩ => exact plane457GenIndicatorBlock3
  | ⟨4, _⟩ => exact plane457GenIndicatorBlock4
  | ⟨5, _⟩ => exact plane457GenIndicatorBlock5
  | ⟨k + 6, h⟩ => omega
end QiushiMatmul
