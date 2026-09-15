import QiushiGlobalOrbitUnused184SectionBlock0
import QiushiGlobalOrbitUnused184SectionBlock1
import QiushiGlobalOrbitUnused184SectionBlock2
import QiushiGlobalOrbitUnused184SectionBlock3
import QiushiGlobalOrbitUnused184SectionBlock4
import QiushiGlobalOrbitUnused184SectionBlock5
import QiushiGlobalOrbitUnused184SectionBlock6
import QiushiGlobalOrbitUnused184SectionBlock7
import QiushiGlobalOrbitUnused184SectionBlock8
import QiushiGlobalOrbitUnused184SectionBlock9
import QiushiGlobalOrbitUnused184SectionBlock10
import QiushiGlobalOrbitUnused184SectionBlock11
import QiushiGlobalOrbitUnused184SectionBlock12
import QiushiGlobalOrbitUnused184SectionBlock13
import QiushiGlobalOrbitUnused184SectionBlock14
import QiushiGlobalOrbitUnused184SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane184UnusedGenSectionAll : forall i, plane184UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane184UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane184UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane184UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane184UnusedGenSectionBlock3
  | ⟨4, _⟩ => exact plane184UnusedGenSectionBlock4
  | ⟨5, _⟩ => exact plane184UnusedGenSectionBlock5
  | ⟨6, _⟩ => exact plane184UnusedGenSectionBlock6
  | ⟨7, _⟩ => exact plane184UnusedGenSectionBlock7
  | ⟨8, _⟩ => exact plane184UnusedGenSectionBlock8
  | ⟨9, _⟩ => exact plane184UnusedGenSectionBlock9
  | ⟨10, _⟩ => exact plane184UnusedGenSectionBlock10
  | ⟨11, _⟩ => exact plane184UnusedGenSectionBlock11
  | ⟨12, _⟩ => exact plane184UnusedGenSectionBlock12
  | ⟨13, _⟩ => exact plane184UnusedGenSectionBlock13
  | ⟨14, _⟩ => exact plane184UnusedGenSectionBlock14
  | ⟨15, _⟩ => exact plane184UnusedGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
