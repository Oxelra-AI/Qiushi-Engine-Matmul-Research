import QiushiGlobalOrbitUnused284SectionBlock0
import QiushiGlobalOrbitUnused284SectionBlock1
import QiushiGlobalOrbitUnused284SectionBlock2
import QiushiGlobalOrbitUnused284SectionBlock3
import QiushiGlobalOrbitUnused284SectionBlock4
import QiushiGlobalOrbitUnused284SectionBlock5
import QiushiGlobalOrbitUnused284SectionBlock6
import QiushiGlobalOrbitUnused284SectionBlock7
import QiushiGlobalOrbitUnused284SectionBlock8
import QiushiGlobalOrbitUnused284SectionBlock9
import QiushiGlobalOrbitUnused284SectionBlock10
import QiushiGlobalOrbitUnused284SectionBlock11
import QiushiGlobalOrbitUnused284SectionBlock12
import QiushiGlobalOrbitUnused284SectionBlock13
import QiushiGlobalOrbitUnused284SectionBlock14
import QiushiGlobalOrbitUnused284SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane284UnusedGenSectionAll : forall i, plane284UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane284UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane284UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane284UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane284UnusedGenSectionBlock3
  | ⟨4, _⟩ => exact plane284UnusedGenSectionBlock4
  | ⟨5, _⟩ => exact plane284UnusedGenSectionBlock5
  | ⟨6, _⟩ => exact plane284UnusedGenSectionBlock6
  | ⟨7, _⟩ => exact plane284UnusedGenSectionBlock7
  | ⟨8, _⟩ => exact plane284UnusedGenSectionBlock8
  | ⟨9, _⟩ => exact plane284UnusedGenSectionBlock9
  | ⟨10, _⟩ => exact plane284UnusedGenSectionBlock10
  | ⟨11, _⟩ => exact plane284UnusedGenSectionBlock11
  | ⟨12, _⟩ => exact plane284UnusedGenSectionBlock12
  | ⟨13, _⟩ => exact plane284UnusedGenSectionBlock13
  | ⟨14, _⟩ => exact plane284UnusedGenSectionBlock14
  | ⟨15, _⟩ => exact plane284UnusedGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
