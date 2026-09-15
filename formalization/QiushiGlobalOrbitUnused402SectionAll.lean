import QiushiGlobalOrbitUnused402SectionBlock0
import QiushiGlobalOrbitUnused402SectionBlock1
import QiushiGlobalOrbitUnused402SectionBlock2
import QiushiGlobalOrbitUnused402SectionBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane402UnusedGenSectionAll : forall i, plane402UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane402UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane402UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane402UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane402UnusedGenSectionBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
