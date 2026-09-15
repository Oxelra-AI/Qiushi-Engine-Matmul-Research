import QiushiPlane454GenIndicatorBlock0
import QiushiPlane454GenIndicatorBlock1
import QiushiPlane454GenIndicatorBlock2
import QiushiPlane454GenIndicatorBlock3
import QiushiPlane454GenIndicatorBlock4
import QiushiPlane454GenIndicatorBlock5
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane454GenIndicatorAll : forall i, plane454GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 6) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane454GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane454GenIndicatorBlock1
  | ⟨2, _⟩ => exact plane454GenIndicatorBlock2
  | ⟨3, _⟩ => exact plane454GenIndicatorBlock3
  | ⟨4, _⟩ => exact plane454GenIndicatorBlock4
  | ⟨5, _⟩ => exact plane454GenIndicatorBlock5
  | ⟨k + 6, h⟩ => omega
end QiushiMatmul
