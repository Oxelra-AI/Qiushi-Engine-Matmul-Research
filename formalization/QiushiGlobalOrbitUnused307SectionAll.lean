import QiushiGlobalOrbitUnused307SectionBlock0
import QiushiGlobalOrbitUnused307SectionBlock1
import QiushiGlobalOrbitUnused307SectionBlock2
import QiushiGlobalOrbitUnused307SectionBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane307UnusedGenSectionAll : forall i, plane307UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane307UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane307UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane307UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane307UnusedGenSectionBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
