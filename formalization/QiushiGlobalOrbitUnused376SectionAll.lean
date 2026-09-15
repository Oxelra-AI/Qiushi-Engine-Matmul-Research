import QiushiGlobalOrbitUnused376SectionBlock0
import QiushiGlobalOrbitUnused376SectionBlock1
import QiushiGlobalOrbitUnused376SectionBlock2
import QiushiGlobalOrbitUnused376SectionBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane376UnusedGenSectionAll : forall i, plane376UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane376UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane376UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane376UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane376UnusedGenSectionBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
