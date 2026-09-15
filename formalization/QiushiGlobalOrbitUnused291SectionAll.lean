import QiushiGlobalOrbitUnused291SectionBlock0
import QiushiGlobalOrbitUnused291SectionBlock1
import QiushiGlobalOrbitUnused291SectionBlock2
import QiushiGlobalOrbitUnused291SectionBlock3
import QiushiGlobalOrbitUnused291SectionBlock4
import QiushiGlobalOrbitUnused291SectionBlock5
import QiushiGlobalOrbitUnused291SectionBlock6
import QiushiGlobalOrbitUnused291SectionBlock7
import QiushiGlobalOrbitUnused291SectionBlock8
import QiushiGlobalOrbitUnused291SectionBlock9
import QiushiGlobalOrbitUnused291SectionBlock10
import QiushiGlobalOrbitUnused291SectionBlock11
import QiushiGlobalOrbitUnused291SectionBlock12
import QiushiGlobalOrbitUnused291SectionBlock13
import QiushiGlobalOrbitUnused291SectionBlock14
import QiushiGlobalOrbitUnused291SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane291UnusedGenSectionAll : forall i, plane291UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane291UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane291UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane291UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane291UnusedGenSectionBlock3
  | ⟨4, _⟩ => exact plane291UnusedGenSectionBlock4
  | ⟨5, _⟩ => exact plane291UnusedGenSectionBlock5
  | ⟨6, _⟩ => exact plane291UnusedGenSectionBlock6
  | ⟨7, _⟩ => exact plane291UnusedGenSectionBlock7
  | ⟨8, _⟩ => exact plane291UnusedGenSectionBlock8
  | ⟨9, _⟩ => exact plane291UnusedGenSectionBlock9
  | ⟨10, _⟩ => exact plane291UnusedGenSectionBlock10
  | ⟨11, _⟩ => exact plane291UnusedGenSectionBlock11
  | ⟨12, _⟩ => exact plane291UnusedGenSectionBlock12
  | ⟨13, _⟩ => exact plane291UnusedGenSectionBlock13
  | ⟨14, _⟩ => exact plane291UnusedGenSectionBlock14
  | ⟨15, _⟩ => exact plane291UnusedGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
