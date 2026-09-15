import QiushiGlobalOrbitUnused395SectionBlock0
import QiushiGlobalOrbitUnused395SectionBlock1
import QiushiGlobalOrbitUnused395SectionBlock2
import QiushiGlobalOrbitUnused395SectionBlock3
import QiushiGlobalOrbitUnused395SectionBlock4
import QiushiGlobalOrbitUnused395SectionBlock5
import QiushiGlobalOrbitUnused395SectionBlock6
import QiushiGlobalOrbitUnused395SectionBlock7
import QiushiGlobalOrbitUnused395SectionBlock8
import QiushiGlobalOrbitUnused395SectionBlock9
import QiushiGlobalOrbitUnused395SectionBlock10
import QiushiGlobalOrbitUnused395SectionBlock11
import QiushiGlobalOrbitUnused395SectionBlock12
import QiushiGlobalOrbitUnused395SectionBlock13
import QiushiGlobalOrbitUnused395SectionBlock14
import QiushiGlobalOrbitUnused395SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane395UnusedGenSectionAll : forall i, plane395UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane395UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane395UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane395UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane395UnusedGenSectionBlock3
  | ⟨4, _⟩ => exact plane395UnusedGenSectionBlock4
  | ⟨5, _⟩ => exact plane395UnusedGenSectionBlock5
  | ⟨6, _⟩ => exact plane395UnusedGenSectionBlock6
  | ⟨7, _⟩ => exact plane395UnusedGenSectionBlock7
  | ⟨8, _⟩ => exact plane395UnusedGenSectionBlock8
  | ⟨9, _⟩ => exact plane395UnusedGenSectionBlock9
  | ⟨10, _⟩ => exact plane395UnusedGenSectionBlock10
  | ⟨11, _⟩ => exact plane395UnusedGenSectionBlock11
  | ⟨12, _⟩ => exact plane395UnusedGenSectionBlock12
  | ⟨13, _⟩ => exact plane395UnusedGenSectionBlock13
  | ⟨14, _⟩ => exact plane395UnusedGenSectionBlock14
  | ⟨15, _⟩ => exact plane395UnusedGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
