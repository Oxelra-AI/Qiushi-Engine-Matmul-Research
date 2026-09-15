import QiushiGlobalOrbitUnused396SectionBlock0
import QiushiGlobalOrbitUnused396SectionBlock1
import QiushiGlobalOrbitUnused396SectionBlock2
import QiushiGlobalOrbitUnused396SectionBlock3
import QiushiGlobalOrbitUnused396SectionBlock4
import QiushiGlobalOrbitUnused396SectionBlock5
import QiushiGlobalOrbitUnused396SectionBlock6
import QiushiGlobalOrbitUnused396SectionBlock7
import QiushiGlobalOrbitUnused396SectionBlock8
import QiushiGlobalOrbitUnused396SectionBlock9
import QiushiGlobalOrbitUnused396SectionBlock10
import QiushiGlobalOrbitUnused396SectionBlock11
import QiushiGlobalOrbitUnused396SectionBlock12
import QiushiGlobalOrbitUnused396SectionBlock13
import QiushiGlobalOrbitUnused396SectionBlock14
import QiushiGlobalOrbitUnused396SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane396UnusedGenSectionAll : forall i, plane396UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane396UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane396UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane396UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane396UnusedGenSectionBlock3
  | ⟨4, _⟩ => exact plane396UnusedGenSectionBlock4
  | ⟨5, _⟩ => exact plane396UnusedGenSectionBlock5
  | ⟨6, _⟩ => exact plane396UnusedGenSectionBlock6
  | ⟨7, _⟩ => exact plane396UnusedGenSectionBlock7
  | ⟨8, _⟩ => exact plane396UnusedGenSectionBlock8
  | ⟨9, _⟩ => exact plane396UnusedGenSectionBlock9
  | ⟨10, _⟩ => exact plane396UnusedGenSectionBlock10
  | ⟨11, _⟩ => exact plane396UnusedGenSectionBlock11
  | ⟨12, _⟩ => exact plane396UnusedGenSectionBlock12
  | ⟨13, _⟩ => exact plane396UnusedGenSectionBlock13
  | ⟨14, _⟩ => exact plane396UnusedGenSectionBlock14
  | ⟨15, _⟩ => exact plane396UnusedGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
