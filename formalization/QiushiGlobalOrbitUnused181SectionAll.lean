import QiushiGlobalOrbitUnused181SectionBlock0
import QiushiGlobalOrbitUnused181SectionBlock1
import QiushiGlobalOrbitUnused181SectionBlock2
import QiushiGlobalOrbitUnused181SectionBlock3
import QiushiGlobalOrbitUnused181SectionBlock4
import QiushiGlobalOrbitUnused181SectionBlock5
import QiushiGlobalOrbitUnused181SectionBlock6
import QiushiGlobalOrbitUnused181SectionBlock7
import QiushiGlobalOrbitUnused181SectionBlock8
import QiushiGlobalOrbitUnused181SectionBlock9
import QiushiGlobalOrbitUnused181SectionBlock10
import QiushiGlobalOrbitUnused181SectionBlock11
import QiushiGlobalOrbitUnused181SectionBlock12
import QiushiGlobalOrbitUnused181SectionBlock13
import QiushiGlobalOrbitUnused181SectionBlock14
import QiushiGlobalOrbitUnused181SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane181UnusedGenSectionAll : forall i, plane181UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane181UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane181UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane181UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane181UnusedGenSectionBlock3
  | ⟨4, _⟩ => exact plane181UnusedGenSectionBlock4
  | ⟨5, _⟩ => exact plane181UnusedGenSectionBlock5
  | ⟨6, _⟩ => exact plane181UnusedGenSectionBlock6
  | ⟨7, _⟩ => exact plane181UnusedGenSectionBlock7
  | ⟨8, _⟩ => exact plane181UnusedGenSectionBlock8
  | ⟨9, _⟩ => exact plane181UnusedGenSectionBlock9
  | ⟨10, _⟩ => exact plane181UnusedGenSectionBlock10
  | ⟨11, _⟩ => exact plane181UnusedGenSectionBlock11
  | ⟨12, _⟩ => exact plane181UnusedGenSectionBlock12
  | ⟨13, _⟩ => exact plane181UnusedGenSectionBlock13
  | ⟨14, _⟩ => exact plane181UnusedGenSectionBlock14
  | ⟨15, _⟩ => exact plane181UnusedGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
