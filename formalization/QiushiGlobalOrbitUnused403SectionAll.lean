import QiushiGlobalOrbitUnused403SectionBlock0
import QiushiGlobalOrbitUnused403SectionBlock1
import QiushiGlobalOrbitUnused403SectionBlock2
import QiushiGlobalOrbitUnused403SectionBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane403UnusedGenSectionAll : forall i, plane403UnusedGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane403UnusedGenSectionBlock0
  | ⟨1, _⟩ => exact plane403UnusedGenSectionBlock1
  | ⟨2, _⟩ => exact plane403UnusedGenSectionBlock2
  | ⟨3, _⟩ => exact plane403UnusedGenSectionBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
