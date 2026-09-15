import QiushiGlobalOrbitUnused328SectionBlock0
import QiushiGlobalOrbitUnused328SectionBlock1
import QiushiGlobalOrbitUnused328SectionBlock2
import QiushiGlobalOrbitUnused328SectionBlock3
import QiushiGlobalOrbitUnused328SectionBlock4
import QiushiGlobalOrbitUnused328SectionBlock5
import QiushiGlobalOrbitUnused328SectionBlock6
import QiushiGlobalOrbitUnused328SectionBlock7
import QiushiGlobalOrbitUnused328SectionBlock8
import QiushiGlobalOrbitUnused328SectionBlock9
import QiushiGlobalOrbitUnused328SectionBlock10
import QiushiGlobalOrbitUnused328SectionBlock11
import QiushiGlobalOrbitUnused328SectionBlock12
import QiushiGlobalOrbitUnused328SectionBlock13
import QiushiGlobalOrbitUnused328SectionBlock14
import QiushiGlobalOrbitUnused328SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane328UnusedGenSectionAll : forall i, plane328UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane328UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane328UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane328UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane328UnusedGenSectionBlock3
  | ⟨4, _⟩ => exact plane328UnusedGenSectionBlock4
  | ⟨5, _⟩ => exact plane328UnusedGenSectionBlock5
  | ⟨6, _⟩ => exact plane328UnusedGenSectionBlock6
  | ⟨7, _⟩ => exact plane328UnusedGenSectionBlock7
  | ⟨8, _⟩ => exact plane328UnusedGenSectionBlock8
  | ⟨9, _⟩ => exact plane328UnusedGenSectionBlock9
  | ⟨10, _⟩ => exact plane328UnusedGenSectionBlock10
  | ⟨11, _⟩ => exact plane328UnusedGenSectionBlock11
  | ⟨12, _⟩ => exact plane328UnusedGenSectionBlock12
  | ⟨13, _⟩ => exact plane328UnusedGenSectionBlock13
  | ⟨14, _⟩ => exact plane328UnusedGenSectionBlock14
  | ⟨15, _⟩ => exact plane328UnusedGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
