import QiushiPlane275GenSectionBlock0
import QiushiPlane275GenSectionBlock1
import QiushiPlane275GenSectionBlock2
import QiushiPlane275GenSectionBlock3
import QiushiPlane275GenSectionBlock4
import QiushiPlane275GenSectionBlock5
import QiushiPlane275GenSectionBlock6
import QiushiPlane275GenSectionBlock7
import QiushiPlane275GenSectionBlock8
import QiushiPlane275GenSectionBlock9
import QiushiPlane275GenSectionBlock10
import QiushiPlane275GenSectionBlock11
import QiushiPlane275GenSectionBlock12
import QiushiPlane275GenSectionBlock13
import QiushiPlane275GenSectionBlock14
import QiushiPlane275GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane275GenSectionAll : forall i, plane275GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane275GenSectionBlock0
  | ⟨1, _⟩ => exact plane275GenSectionBlock1
  | ⟨2, _⟩ => exact plane275GenSectionBlock2
  | ⟨3, _⟩ => exact plane275GenSectionBlock3
  | ⟨4, _⟩ => exact plane275GenSectionBlock4
  | ⟨5, _⟩ => exact plane275GenSectionBlock5
  | ⟨6, _⟩ => exact plane275GenSectionBlock6
  | ⟨7, _⟩ => exact plane275GenSectionBlock7
  | ⟨8, _⟩ => exact plane275GenSectionBlock8
  | ⟨9, _⟩ => exact plane275GenSectionBlock9
  | ⟨10, _⟩ => exact plane275GenSectionBlock10
  | ⟨11, _⟩ => exact plane275GenSectionBlock11
  | ⟨12, _⟩ => exact plane275GenSectionBlock12
  | ⟨13, _⟩ => exact plane275GenSectionBlock13
  | ⟨14, _⟩ => exact plane275GenSectionBlock14
  | ⟨15, _⟩ => exact plane275GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
