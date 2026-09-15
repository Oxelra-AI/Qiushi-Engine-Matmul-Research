import QiushiGlobalOrbitUnused386SectionBlock0
import QiushiGlobalOrbitUnused386SectionBlock1
import QiushiGlobalOrbitUnused386SectionBlock2
import QiushiGlobalOrbitUnused386SectionBlock3
import QiushiGlobalOrbitUnused386SectionBlock4
import QiushiGlobalOrbitUnused386SectionBlock5
import QiushiGlobalOrbitUnused386SectionBlock6
import QiushiGlobalOrbitUnused386SectionBlock7
import QiushiGlobalOrbitUnused386SectionBlock8
import QiushiGlobalOrbitUnused386SectionBlock9
import QiushiGlobalOrbitUnused386SectionBlock10
import QiushiGlobalOrbitUnused386SectionBlock11
import QiushiGlobalOrbitUnused386SectionBlock12
import QiushiGlobalOrbitUnused386SectionBlock13
import QiushiGlobalOrbitUnused386SectionBlock14
import QiushiGlobalOrbitUnused386SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane386UnusedGenSectionAll : forall i, plane386UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane386UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane386UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane386UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane386UnusedGenSectionBlock3
  | ⟨4, _⟩ => exact plane386UnusedGenSectionBlock4
  | ⟨5, _⟩ => exact plane386UnusedGenSectionBlock5
  | ⟨6, _⟩ => exact plane386UnusedGenSectionBlock6
  | ⟨7, _⟩ => exact plane386UnusedGenSectionBlock7
  | ⟨8, _⟩ => exact plane386UnusedGenSectionBlock8
  | ⟨9, _⟩ => exact plane386UnusedGenSectionBlock9
  | ⟨10, _⟩ => exact plane386UnusedGenSectionBlock10
  | ⟨11, _⟩ => exact plane386UnusedGenSectionBlock11
  | ⟨12, _⟩ => exact plane386UnusedGenSectionBlock12
  | ⟨13, _⟩ => exact plane386UnusedGenSectionBlock13
  | ⟨14, _⟩ => exact plane386UnusedGenSectionBlock14
  | ⟨15, _⟩ => exact plane386UnusedGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
