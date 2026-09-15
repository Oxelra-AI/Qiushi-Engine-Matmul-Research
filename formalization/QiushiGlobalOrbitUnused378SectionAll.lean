import QiushiGlobalOrbitUnused378SectionBlock0
import QiushiGlobalOrbitUnused378SectionBlock1
import QiushiGlobalOrbitUnused378SectionBlock2
import QiushiGlobalOrbitUnused378SectionBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane378UnusedGenSectionAll : forall i, plane378UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane378UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane378UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane378UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane378UnusedGenSectionBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
