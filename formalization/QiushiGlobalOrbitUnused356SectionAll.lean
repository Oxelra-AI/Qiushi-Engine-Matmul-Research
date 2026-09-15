import QiushiGlobalOrbitUnused356SectionBlock0
import QiushiGlobalOrbitUnused356SectionBlock1
import QiushiGlobalOrbitUnused356SectionBlock2
import QiushiGlobalOrbitUnused356SectionBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane356UnusedGenSectionAll : forall i, plane356UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane356UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane356UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane356UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane356UnusedGenSectionBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
