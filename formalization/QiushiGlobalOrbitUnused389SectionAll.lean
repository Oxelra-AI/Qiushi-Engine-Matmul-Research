import QiushiGlobalOrbitUnused389SectionBlock0
import QiushiGlobalOrbitUnused389SectionBlock1
import QiushiGlobalOrbitUnused389SectionBlock2
import QiushiGlobalOrbitUnused389SectionBlock3
import QiushiGlobalOrbitUnused389SectionBlock4
import QiushiGlobalOrbitUnused389SectionBlock5
import QiushiGlobalOrbitUnused389SectionBlock6
import QiushiGlobalOrbitUnused389SectionBlock7
import QiushiGlobalOrbitUnused389SectionBlock8
import QiushiGlobalOrbitUnused389SectionBlock9
import QiushiGlobalOrbitUnused389SectionBlock10
import QiushiGlobalOrbitUnused389SectionBlock11
import QiushiGlobalOrbitUnused389SectionBlock12
import QiushiGlobalOrbitUnused389SectionBlock13
import QiushiGlobalOrbitUnused389SectionBlock14
import QiushiGlobalOrbitUnused389SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane389UnusedGenSectionAll : forall i, plane389UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane389UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane389UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane389UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane389UnusedGenSectionBlock3
  | ⟨4, _⟩ => exact plane389UnusedGenSectionBlock4
  | ⟨5, _⟩ => exact plane389UnusedGenSectionBlock5
  | ⟨6, _⟩ => exact plane389UnusedGenSectionBlock6
  | ⟨7, _⟩ => exact plane389UnusedGenSectionBlock7
  | ⟨8, _⟩ => exact plane389UnusedGenSectionBlock8
  | ⟨9, _⟩ => exact plane389UnusedGenSectionBlock9
  | ⟨10, _⟩ => exact plane389UnusedGenSectionBlock10
  | ⟨11, _⟩ => exact plane389UnusedGenSectionBlock11
  | ⟨12, _⟩ => exact plane389UnusedGenSectionBlock12
  | ⟨13, _⟩ => exact plane389UnusedGenSectionBlock13
  | ⟨14, _⟩ => exact plane389UnusedGenSectionBlock14
  | ⟨15, _⟩ => exact plane389UnusedGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
