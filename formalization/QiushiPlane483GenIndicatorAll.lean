import QiushiPlane483GenIndicatorBlock0
import QiushiPlane483GenIndicatorBlock1
import QiushiPlane483GenIndicatorBlock2
import QiushiPlane483GenIndicatorBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane483GenIndicatorAll : forall i, plane483GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane483GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane483GenIndicatorBlock1
  | ⟨2, _⟩ => exact plane483GenIndicatorBlock2
  | ⟨3, _⟩ => exact plane483GenIndicatorBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
