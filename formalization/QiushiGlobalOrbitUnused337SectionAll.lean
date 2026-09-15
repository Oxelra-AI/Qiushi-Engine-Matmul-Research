import QiushiGlobalOrbitUnused337SectionBlock0
import QiushiGlobalOrbitUnused337SectionBlock1
import QiushiGlobalOrbitUnused337SectionBlock2
import QiushiGlobalOrbitUnused337SectionBlock3
import QiushiGlobalOrbitUnused337SectionBlock4
import QiushiGlobalOrbitUnused337SectionBlock5
import QiushiGlobalOrbitUnused337SectionBlock6
import QiushiGlobalOrbitUnused337SectionBlock7
import QiushiGlobalOrbitUnused337SectionBlock8
import QiushiGlobalOrbitUnused337SectionBlock9
import QiushiGlobalOrbitUnused337SectionBlock10
import QiushiGlobalOrbitUnused337SectionBlock11
import QiushiGlobalOrbitUnused337SectionBlock12
import QiushiGlobalOrbitUnused337SectionBlock13
import QiushiGlobalOrbitUnused337SectionBlock14
import QiushiGlobalOrbitUnused337SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane337UnusedGenSectionAll : forall i, plane337UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane337UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane337UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane337UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane337UnusedGenSectionBlock3
  | ⟨4, _⟩ => exact plane337UnusedGenSectionBlock4
  | ⟨5, _⟩ => exact plane337UnusedGenSectionBlock5
  | ⟨6, _⟩ => exact plane337UnusedGenSectionBlock6
  | ⟨7, _⟩ => exact plane337UnusedGenSectionBlock7
  | ⟨8, _⟩ => exact plane337UnusedGenSectionBlock8
  | ⟨9, _⟩ => exact plane337UnusedGenSectionBlock9
  | ⟨10, _⟩ => exact plane337UnusedGenSectionBlock10
  | ⟨11, _⟩ => exact plane337UnusedGenSectionBlock11
  | ⟨12, _⟩ => exact plane337UnusedGenSectionBlock12
  | ⟨13, _⟩ => exact plane337UnusedGenSectionBlock13
  | ⟨14, _⟩ => exact plane337UnusedGenSectionBlock14
  | ⟨15, _⟩ => exact plane337UnusedGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
