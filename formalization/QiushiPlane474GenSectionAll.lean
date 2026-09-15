import QiushiPlane474GenSectionBlock0
import QiushiPlane474GenSectionBlock1
import QiushiPlane474GenSectionBlock2
import QiushiPlane474GenSectionBlock3
import QiushiPlane474GenSectionBlock4
import QiushiPlane474GenSectionBlock5
import QiushiPlane474GenSectionBlock6
import QiushiPlane474GenSectionBlock7
import QiushiPlane474GenSectionBlock8
import QiushiPlane474GenSectionBlock9
import QiushiPlane474GenSectionBlock10
import QiushiPlane474GenSectionBlock11
import QiushiPlane474GenSectionBlock12
import QiushiPlane474GenSectionBlock13
import QiushiPlane474GenSectionBlock14
import QiushiPlane474GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane474GenSectionAll : forall i, plane474GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane474GenSectionBlock0
  | ⟨1, _⟩ => exact plane474GenSectionBlock1
  | ⟨2, _⟩ => exact plane474GenSectionBlock2
  | ⟨3, _⟩ => exact plane474GenSectionBlock3
  | ⟨4, _⟩ => exact plane474GenSectionBlock4
  | ⟨5, _⟩ => exact plane474GenSectionBlock5
  | ⟨6, _⟩ => exact plane474GenSectionBlock6
  | ⟨7, _⟩ => exact plane474GenSectionBlock7
  | ⟨8, _⟩ => exact plane474GenSectionBlock8
  | ⟨9, _⟩ => exact plane474GenSectionBlock9
  | ⟨10, _⟩ => exact plane474GenSectionBlock10
  | ⟨11, _⟩ => exact plane474GenSectionBlock11
  | ⟨12, _⟩ => exact plane474GenSectionBlock12
  | ⟨13, _⟩ => exact plane474GenSectionBlock13
  | ⟨14, _⟩ => exact plane474GenSectionBlock14
  | ⟨15, _⟩ => exact plane474GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
