import QiushiPlane434GenIndicatorBlock0
import QiushiPlane434GenIndicatorBlock1
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane434GenIndicatorAll : forall i, plane434GenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 2) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane434GenIndicatorBlock0
  | ⟨1, _⟩ => exact plane434GenIndicatorBlock1
  | ⟨k + 2, h⟩ => omega
end QiushiMatmul
