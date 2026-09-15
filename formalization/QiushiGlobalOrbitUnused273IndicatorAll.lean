import QiushiGlobalOrbitUnused273IndicatorBlock0
import QiushiGlobalOrbitUnused273IndicatorBlock1
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane273UnusedGenIndicatorAll : forall i, plane273UnusedGenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 2) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane273UnusedGenIndicatorBlock0
  | ⟨1, _⟩ => exact plane273UnusedGenIndicatorBlock1
  | ⟨k + 2, h⟩ => omega
end QiushiMatmul
