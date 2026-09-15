import QiushiPlane336GenSectionBlock0
import QiushiPlane336GenSectionBlock1
import QiushiPlane336GenSectionBlock2
import QiushiPlane336GenSectionBlock3
import QiushiPlane336GenSectionBlock4
import QiushiPlane336GenSectionBlock5
import QiushiPlane336GenSectionBlock6
import QiushiPlane336GenSectionBlock7
import QiushiPlane336GenSectionBlock8
import QiushiPlane336GenSectionBlock9
import QiushiPlane336GenSectionBlock10
import QiushiPlane336GenSectionBlock11
import QiushiPlane336GenSectionBlock12
import QiushiPlane336GenSectionBlock13
import QiushiPlane336GenSectionBlock14
import QiushiPlane336GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane336GenSectionAll : forall i, plane336GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane336GenSectionBlock0
  | ⟨1, _⟩ => exact plane336GenSectionBlock1
  | ⟨2, _⟩ => exact plane336GenSectionBlock2
  | ⟨3, _⟩ => exact plane336GenSectionBlock3
  | ⟨4, _⟩ => exact plane336GenSectionBlock4
  | ⟨5, _⟩ => exact plane336GenSectionBlock5
  | ⟨6, _⟩ => exact plane336GenSectionBlock6
  | ⟨7, _⟩ => exact plane336GenSectionBlock7
  | ⟨8, _⟩ => exact plane336GenSectionBlock8
  | ⟨9, _⟩ => exact plane336GenSectionBlock9
  | ⟨10, _⟩ => exact plane336GenSectionBlock10
  | ⟨11, _⟩ => exact plane336GenSectionBlock11
  | ⟨12, _⟩ => exact plane336GenSectionBlock12
  | ⟨13, _⟩ => exact plane336GenSectionBlock13
  | ⟨14, _⟩ => exact plane336GenSectionBlock14
  | ⟨15, _⟩ => exact plane336GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
