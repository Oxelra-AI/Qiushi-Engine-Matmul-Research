import QiushiGlobalOrbitUnused248SectionBlock0
import QiushiGlobalOrbitUnused248SectionBlock1
import QiushiGlobalOrbitUnused248SectionBlock2
import QiushiGlobalOrbitUnused248SectionBlock3
import QiushiGlobalOrbitUnused248SectionBlock4
import QiushiGlobalOrbitUnused248SectionBlock5
import QiushiGlobalOrbitUnused248SectionBlock6
import QiushiGlobalOrbitUnused248SectionBlock7
import QiushiGlobalOrbitUnused248SectionBlock8
import QiushiGlobalOrbitUnused248SectionBlock9
import QiushiGlobalOrbitUnused248SectionBlock10
import QiushiGlobalOrbitUnused248SectionBlock11
import QiushiGlobalOrbitUnused248SectionBlock12
import QiushiGlobalOrbitUnused248SectionBlock13
import QiushiGlobalOrbitUnused248SectionBlock14
import QiushiGlobalOrbitUnused248SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane248UnusedGenSectionAll : forall i, plane248UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane248UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane248UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane248UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane248UnusedGenSectionBlock3
  | ⟨4, _⟩ => exact plane248UnusedGenSectionBlock4
  | ⟨5, _⟩ => exact plane248UnusedGenSectionBlock5
  | ⟨6, _⟩ => exact plane248UnusedGenSectionBlock6
  | ⟨7, _⟩ => exact plane248UnusedGenSectionBlock7
  | ⟨8, _⟩ => exact plane248UnusedGenSectionBlock8
  | ⟨9, _⟩ => exact plane248UnusedGenSectionBlock9
  | ⟨10, _⟩ => exact plane248UnusedGenSectionBlock10
  | ⟨11, _⟩ => exact plane248UnusedGenSectionBlock11
  | ⟨12, _⟩ => exact plane248UnusedGenSectionBlock12
  | ⟨13, _⟩ => exact plane248UnusedGenSectionBlock13
  | ⟨14, _⟩ => exact plane248UnusedGenSectionBlock14
  | ⟨15, _⟩ => exact plane248UnusedGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
