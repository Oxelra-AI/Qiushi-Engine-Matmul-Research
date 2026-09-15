import QiushiGlobalOrbitUnused249SectionBlock0
import QiushiGlobalOrbitUnused249SectionBlock1
import QiushiGlobalOrbitUnused249SectionBlock2
import QiushiGlobalOrbitUnused249SectionBlock3
import QiushiGlobalOrbitUnused249SectionBlock4
import QiushiGlobalOrbitUnused249SectionBlock5
import QiushiGlobalOrbitUnused249SectionBlock6
import QiushiGlobalOrbitUnused249SectionBlock7
import QiushiGlobalOrbitUnused249SectionBlock8
import QiushiGlobalOrbitUnused249SectionBlock9
import QiushiGlobalOrbitUnused249SectionBlock10
import QiushiGlobalOrbitUnused249SectionBlock11
import QiushiGlobalOrbitUnused249SectionBlock12
import QiushiGlobalOrbitUnused249SectionBlock13
import QiushiGlobalOrbitUnused249SectionBlock14
import QiushiGlobalOrbitUnused249SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane249UnusedGenSectionAll : forall i, plane249UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane249UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane249UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane249UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane249UnusedGenSectionBlock3
  | ⟨4, _⟩ => exact plane249UnusedGenSectionBlock4
  | ⟨5, _⟩ => exact plane249UnusedGenSectionBlock5
  | ⟨6, _⟩ => exact plane249UnusedGenSectionBlock6
  | ⟨7, _⟩ => exact plane249UnusedGenSectionBlock7
  | ⟨8, _⟩ => exact plane249UnusedGenSectionBlock8
  | ⟨9, _⟩ => exact plane249UnusedGenSectionBlock9
  | ⟨10, _⟩ => exact plane249UnusedGenSectionBlock10
  | ⟨11, _⟩ => exact plane249UnusedGenSectionBlock11
  | ⟨12, _⟩ => exact plane249UnusedGenSectionBlock12
  | ⟨13, _⟩ => exact plane249UnusedGenSectionBlock13
  | ⟨14, _⟩ => exact plane249UnusedGenSectionBlock14
  | ⟨15, _⟩ => exact plane249UnusedGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
