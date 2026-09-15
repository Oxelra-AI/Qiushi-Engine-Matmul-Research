import QiushiGlobalOrbitUnused355SectionBlock0
import QiushiGlobalOrbitUnused355SectionBlock1
import QiushiGlobalOrbitUnused355SectionBlock2
import QiushiGlobalOrbitUnused355SectionBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane355UnusedGenSectionAll : forall i, plane355UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane355UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane355UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane355UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane355UnusedGenSectionBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
