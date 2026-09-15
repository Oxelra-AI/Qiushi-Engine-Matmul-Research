import QiushiGlobalOrbitUnused305SectionBlock0
import QiushiGlobalOrbitUnused305SectionBlock1
import QiushiGlobalOrbitUnused305SectionBlock2
import QiushiGlobalOrbitUnused305SectionBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane305UnusedGenSectionAll : forall i, plane305UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane305UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane305UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane305UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane305UnusedGenSectionBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
