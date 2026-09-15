import QiushiGlobalOrbitUnused404SectionBlock0
import QiushiGlobalOrbitUnused404SectionBlock1
import QiushiGlobalOrbitUnused404SectionBlock2
import QiushiGlobalOrbitUnused404SectionBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane404UnusedGenSectionAll : forall i, plane404UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane404UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane404UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane404UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane404UnusedGenSectionBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
