import QiushiPlane430GenSectionBlock0
import QiushiPlane430GenSectionBlock1
import QiushiPlane430GenSectionBlock2
import QiushiPlane430GenSectionBlock3
import QiushiPlane430GenSectionBlock4
import QiushiPlane430GenSectionBlock5
import QiushiPlane430GenSectionBlock6
import QiushiPlane430GenSectionBlock7
import QiushiPlane430GenSectionBlock8
import QiushiPlane430GenSectionBlock9
import QiushiPlane430GenSectionBlock10
import QiushiPlane430GenSectionBlock11
import QiushiPlane430GenSectionBlock12
import QiushiPlane430GenSectionBlock13
import QiushiPlane430GenSectionBlock14
import QiushiPlane430GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane430GenSectionAll : forall i, plane430GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane430GenSectionBlock0
  | ⟨1, _⟩ => exact plane430GenSectionBlock1
  | ⟨2, _⟩ => exact plane430GenSectionBlock2
  | ⟨3, _⟩ => exact plane430GenSectionBlock3
  | ⟨4, _⟩ => exact plane430GenSectionBlock4
  | ⟨5, _⟩ => exact plane430GenSectionBlock5
  | ⟨6, _⟩ => exact plane430GenSectionBlock6
  | ⟨7, _⟩ => exact plane430GenSectionBlock7
  | ⟨8, _⟩ => exact plane430GenSectionBlock8
  | ⟨9, _⟩ => exact plane430GenSectionBlock9
  | ⟨10, _⟩ => exact plane430GenSectionBlock10
  | ⟨11, _⟩ => exact plane430GenSectionBlock11
  | ⟨12, _⟩ => exact plane430GenSectionBlock12
  | ⟨13, _⟩ => exact plane430GenSectionBlock13
  | ⟨14, _⟩ => exact plane430GenSectionBlock14
  | ⟨15, _⟩ => exact plane430GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
