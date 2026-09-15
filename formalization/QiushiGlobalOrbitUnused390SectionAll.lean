import QiushiGlobalOrbitUnused390SectionBlock0
import QiushiGlobalOrbitUnused390SectionBlock1
import QiushiGlobalOrbitUnused390SectionBlock2
import QiushiGlobalOrbitUnused390SectionBlock3
import QiushiGlobalOrbitUnused390SectionBlock4
import QiushiGlobalOrbitUnused390SectionBlock5
import QiushiGlobalOrbitUnused390SectionBlock6
import QiushiGlobalOrbitUnused390SectionBlock7
import QiushiGlobalOrbitUnused390SectionBlock8
import QiushiGlobalOrbitUnused390SectionBlock9
import QiushiGlobalOrbitUnused390SectionBlock10
import QiushiGlobalOrbitUnused390SectionBlock11
import QiushiGlobalOrbitUnused390SectionBlock12
import QiushiGlobalOrbitUnused390SectionBlock13
import QiushiGlobalOrbitUnused390SectionBlock14
import QiushiGlobalOrbitUnused390SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane390UnusedGenSectionAll : forall i, plane390UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane390UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane390UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane390UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane390UnusedGenSectionBlock3
  | ⟨4, _⟩ => exact plane390UnusedGenSectionBlock4
  | ⟨5, _⟩ => exact plane390UnusedGenSectionBlock5
  | ⟨6, _⟩ => exact plane390UnusedGenSectionBlock6
  | ⟨7, _⟩ => exact plane390UnusedGenSectionBlock7
  | ⟨8, _⟩ => exact plane390UnusedGenSectionBlock8
  | ⟨9, _⟩ => exact plane390UnusedGenSectionBlock9
  | ⟨10, _⟩ => exact plane390UnusedGenSectionBlock10
  | ⟨11, _⟩ => exact plane390UnusedGenSectionBlock11
  | ⟨12, _⟩ => exact plane390UnusedGenSectionBlock12
  | ⟨13, _⟩ => exact plane390UnusedGenSectionBlock13
  | ⟨14, _⟩ => exact plane390UnusedGenSectionBlock14
  | ⟨15, _⟩ => exact plane390UnusedGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
