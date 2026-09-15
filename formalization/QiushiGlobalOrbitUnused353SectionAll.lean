import QiushiGlobalOrbitUnused353SectionBlock0
import QiushiGlobalOrbitUnused353SectionBlock1
import QiushiGlobalOrbitUnused353SectionBlock2
import QiushiGlobalOrbitUnused353SectionBlock3
import QiushiGlobalOrbitUnused353SectionBlock4
import QiushiGlobalOrbitUnused353SectionBlock5
import QiushiGlobalOrbitUnused353SectionBlock6
import QiushiGlobalOrbitUnused353SectionBlock7
import QiushiGlobalOrbitUnused353SectionBlock8
import QiushiGlobalOrbitUnused353SectionBlock9
import QiushiGlobalOrbitUnused353SectionBlock10
import QiushiGlobalOrbitUnused353SectionBlock11
import QiushiGlobalOrbitUnused353SectionBlock12
import QiushiGlobalOrbitUnused353SectionBlock13
import QiushiGlobalOrbitUnused353SectionBlock14
import QiushiGlobalOrbitUnused353SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane353UnusedGenSectionAll : forall i, plane353UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane353UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane353UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane353UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane353UnusedGenSectionBlock3
  | ⟨4, _⟩ => exact plane353UnusedGenSectionBlock4
  | ⟨5, _⟩ => exact plane353UnusedGenSectionBlock5
  | ⟨6, _⟩ => exact plane353UnusedGenSectionBlock6
  | ⟨7, _⟩ => exact plane353UnusedGenSectionBlock7
  | ⟨8, _⟩ => exact plane353UnusedGenSectionBlock8
  | ⟨9, _⟩ => exact plane353UnusedGenSectionBlock9
  | ⟨10, _⟩ => exact plane353UnusedGenSectionBlock10
  | ⟨11, _⟩ => exact plane353UnusedGenSectionBlock11
  | ⟨12, _⟩ => exact plane353UnusedGenSectionBlock12
  | ⟨13, _⟩ => exact plane353UnusedGenSectionBlock13
  | ⟨14, _⟩ => exact plane353UnusedGenSectionBlock14
  | ⟨15, _⟩ => exact plane353UnusedGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
