import QiushiGlobalOrbitUnused388SectionBlock0
import QiushiGlobalOrbitUnused388SectionBlock1
import QiushiGlobalOrbitUnused388SectionBlock2
import QiushiGlobalOrbitUnused388SectionBlock3
import QiushiGlobalOrbitUnused388SectionBlock4
import QiushiGlobalOrbitUnused388SectionBlock5
import QiushiGlobalOrbitUnused388SectionBlock6
import QiushiGlobalOrbitUnused388SectionBlock7
import QiushiGlobalOrbitUnused388SectionBlock8
import QiushiGlobalOrbitUnused388SectionBlock9
import QiushiGlobalOrbitUnused388SectionBlock10
import QiushiGlobalOrbitUnused388SectionBlock11
import QiushiGlobalOrbitUnused388SectionBlock12
import QiushiGlobalOrbitUnused388SectionBlock13
import QiushiGlobalOrbitUnused388SectionBlock14
import QiushiGlobalOrbitUnused388SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane388UnusedGenSectionAll : forall i, plane388UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane388UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane388UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane388UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane388UnusedGenSectionBlock3
  | ⟨4, _⟩ => exact plane388UnusedGenSectionBlock4
  | ⟨5, _⟩ => exact plane388UnusedGenSectionBlock5
  | ⟨6, _⟩ => exact plane388UnusedGenSectionBlock6
  | ⟨7, _⟩ => exact plane388UnusedGenSectionBlock7
  | ⟨8, _⟩ => exact plane388UnusedGenSectionBlock8
  | ⟨9, _⟩ => exact plane388UnusedGenSectionBlock9
  | ⟨10, _⟩ => exact plane388UnusedGenSectionBlock10
  | ⟨11, _⟩ => exact plane388UnusedGenSectionBlock11
  | ⟨12, _⟩ => exact plane388UnusedGenSectionBlock12
  | ⟨13, _⟩ => exact plane388UnusedGenSectionBlock13
  | ⟨14, _⟩ => exact plane388UnusedGenSectionBlock14
  | ⟨15, _⟩ => exact plane388UnusedGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
