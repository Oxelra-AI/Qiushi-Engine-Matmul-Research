import QiushiGlobalOrbitUnused304SectionBlock0
import QiushiGlobalOrbitUnused304SectionBlock1
import QiushiGlobalOrbitUnused304SectionBlock2
import QiushiGlobalOrbitUnused304SectionBlock3
import QiushiGlobalOrbitUnused304SectionBlock4
import QiushiGlobalOrbitUnused304SectionBlock5
import QiushiGlobalOrbitUnused304SectionBlock6
import QiushiGlobalOrbitUnused304SectionBlock7
import QiushiGlobalOrbitUnused304SectionBlock8
import QiushiGlobalOrbitUnused304SectionBlock9
import QiushiGlobalOrbitUnused304SectionBlock10
import QiushiGlobalOrbitUnused304SectionBlock11
import QiushiGlobalOrbitUnused304SectionBlock12
import QiushiGlobalOrbitUnused304SectionBlock13
import QiushiGlobalOrbitUnused304SectionBlock14
import QiushiGlobalOrbitUnused304SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane304UnusedGenSectionAll : forall i, plane304UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane304UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane304UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane304UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane304UnusedGenSectionBlock3
  | ⟨4, _⟩ => exact plane304UnusedGenSectionBlock4
  | ⟨5, _⟩ => exact plane304UnusedGenSectionBlock5
  | ⟨6, _⟩ => exact plane304UnusedGenSectionBlock6
  | ⟨7, _⟩ => exact plane304UnusedGenSectionBlock7
  | ⟨8, _⟩ => exact plane304UnusedGenSectionBlock8
  | ⟨9, _⟩ => exact plane304UnusedGenSectionBlock9
  | ⟨10, _⟩ => exact plane304UnusedGenSectionBlock10
  | ⟨11, _⟩ => exact plane304UnusedGenSectionBlock11
  | ⟨12, _⟩ => exact plane304UnusedGenSectionBlock12
  | ⟨13, _⟩ => exact plane304UnusedGenSectionBlock13
  | ⟨14, _⟩ => exact plane304UnusedGenSectionBlock14
  | ⟨15, _⟩ => exact plane304UnusedGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
