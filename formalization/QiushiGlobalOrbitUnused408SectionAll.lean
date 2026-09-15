import QiushiGlobalOrbitUnused408SectionBlock0
import QiushiGlobalOrbitUnused408SectionBlock1
import QiushiGlobalOrbitUnused408SectionBlock2
import QiushiGlobalOrbitUnused408SectionBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane408UnusedGenSectionAll : forall i, plane408UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane408UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane408UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane408UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane408UnusedGenSectionBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
