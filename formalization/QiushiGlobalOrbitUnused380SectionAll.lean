import QiushiGlobalOrbitUnused380SectionBlock0
import QiushiGlobalOrbitUnused380SectionBlock1
import QiushiGlobalOrbitUnused380SectionBlock2
import QiushiGlobalOrbitUnused380SectionBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane380UnusedGenSectionAll : forall i, plane380UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane380UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane380UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane380UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane380UnusedGenSectionBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
