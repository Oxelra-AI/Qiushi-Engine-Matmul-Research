import QiushiGlobalOrbitUnused321SectionBlock0
import QiushiGlobalOrbitUnused321SectionBlock1
import QiushiGlobalOrbitUnused321SectionBlock2
import QiushiGlobalOrbitUnused321SectionBlock3
import QiushiGlobalOrbitUnused321SectionBlock4
import QiushiGlobalOrbitUnused321SectionBlock5
import QiushiGlobalOrbitUnused321SectionBlock6
import QiushiGlobalOrbitUnused321SectionBlock7
import QiushiGlobalOrbitUnused321SectionBlock8
import QiushiGlobalOrbitUnused321SectionBlock9
import QiushiGlobalOrbitUnused321SectionBlock10
import QiushiGlobalOrbitUnused321SectionBlock11
import QiushiGlobalOrbitUnused321SectionBlock12
import QiushiGlobalOrbitUnused321SectionBlock13
import QiushiGlobalOrbitUnused321SectionBlock14
import QiushiGlobalOrbitUnused321SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane321UnusedGenSectionAll : forall i, plane321UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane321UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane321UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane321UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane321UnusedGenSectionBlock3
  | ⟨4, _⟩ => exact plane321UnusedGenSectionBlock4
  | ⟨5, _⟩ => exact plane321UnusedGenSectionBlock5
  | ⟨6, _⟩ => exact plane321UnusedGenSectionBlock6
  | ⟨7, _⟩ => exact plane321UnusedGenSectionBlock7
  | ⟨8, _⟩ => exact plane321UnusedGenSectionBlock8
  | ⟨9, _⟩ => exact plane321UnusedGenSectionBlock9
  | ⟨10, _⟩ => exact plane321UnusedGenSectionBlock10
  | ⟨11, _⟩ => exact plane321UnusedGenSectionBlock11
  | ⟨12, _⟩ => exact plane321UnusedGenSectionBlock12
  | ⟨13, _⟩ => exact plane321UnusedGenSectionBlock13
  | ⟨14, _⟩ => exact plane321UnusedGenSectionBlock14
  | ⟨15, _⟩ => exact plane321UnusedGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
