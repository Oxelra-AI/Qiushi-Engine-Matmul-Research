import QiushiPlane338GenSectionBlock0
import QiushiPlane338GenSectionBlock1
import QiushiPlane338GenSectionBlock2
import QiushiPlane338GenSectionBlock3
import QiushiPlane338GenSectionBlock4
import QiushiPlane338GenSectionBlock5
import QiushiPlane338GenSectionBlock6
import QiushiPlane338GenSectionBlock7
import QiushiPlane338GenSectionBlock8
import QiushiPlane338GenSectionBlock9
import QiushiPlane338GenSectionBlock10
import QiushiPlane338GenSectionBlock11
import QiushiPlane338GenSectionBlock12
import QiushiPlane338GenSectionBlock13
import QiushiPlane338GenSectionBlock14
import QiushiPlane338GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane338GenSectionAll : forall i, plane338GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane338GenSectionBlock0
  | ⟨1, _⟩ => exact plane338GenSectionBlock1
  | ⟨2, _⟩ => exact plane338GenSectionBlock2
  | ⟨3, _⟩ => exact plane338GenSectionBlock3
  | ⟨4, _⟩ => exact plane338GenSectionBlock4
  | ⟨5, _⟩ => exact plane338GenSectionBlock5
  | ⟨6, _⟩ => exact plane338GenSectionBlock6
  | ⟨7, _⟩ => exact plane338GenSectionBlock7
  | ⟨8, _⟩ => exact plane338GenSectionBlock8
  | ⟨9, _⟩ => exact plane338GenSectionBlock9
  | ⟨10, _⟩ => exact plane338GenSectionBlock10
  | ⟨11, _⟩ => exact plane338GenSectionBlock11
  | ⟨12, _⟩ => exact plane338GenSectionBlock12
  | ⟨13, _⟩ => exact plane338GenSectionBlock13
  | ⟨14, _⟩ => exact plane338GenSectionBlock14
  | ⟨15, _⟩ => exact plane338GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
