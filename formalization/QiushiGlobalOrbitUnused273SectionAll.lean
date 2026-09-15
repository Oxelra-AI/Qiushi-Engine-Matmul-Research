import QiushiGlobalOrbitUnused273SectionBlock0
import QiushiGlobalOrbitUnused273SectionBlock1
import QiushiGlobalOrbitUnused273SectionBlock2
import QiushiGlobalOrbitUnused273SectionBlock3
import QiushiGlobalOrbitUnused273SectionBlock4
import QiushiGlobalOrbitUnused273SectionBlock5
import QiushiGlobalOrbitUnused273SectionBlock6
import QiushiGlobalOrbitUnused273SectionBlock7
import QiushiGlobalOrbitUnused273SectionBlock8
import QiushiGlobalOrbitUnused273SectionBlock9
import QiushiGlobalOrbitUnused273SectionBlock10
import QiushiGlobalOrbitUnused273SectionBlock11
import QiushiGlobalOrbitUnused273SectionBlock12
import QiushiGlobalOrbitUnused273SectionBlock13
import QiushiGlobalOrbitUnused273SectionBlock14
import QiushiGlobalOrbitUnused273SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane273UnusedGenSectionAll : forall i, plane273UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane273UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane273UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane273UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane273UnusedGenSectionBlock3
  | ⟨4, _⟩ => exact plane273UnusedGenSectionBlock4
  | ⟨5, _⟩ => exact plane273UnusedGenSectionBlock5
  | ⟨6, _⟩ => exact plane273UnusedGenSectionBlock6
  | ⟨7, _⟩ => exact plane273UnusedGenSectionBlock7
  | ⟨8, _⟩ => exact plane273UnusedGenSectionBlock8
  | ⟨9, _⟩ => exact plane273UnusedGenSectionBlock9
  | ⟨10, _⟩ => exact plane273UnusedGenSectionBlock10
  | ⟨11, _⟩ => exact plane273UnusedGenSectionBlock11
  | ⟨12, _⟩ => exact plane273UnusedGenSectionBlock12
  | ⟨13, _⟩ => exact plane273UnusedGenSectionBlock13
  | ⟨14, _⟩ => exact plane273UnusedGenSectionBlock14
  | ⟨15, _⟩ => exact plane273UnusedGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
