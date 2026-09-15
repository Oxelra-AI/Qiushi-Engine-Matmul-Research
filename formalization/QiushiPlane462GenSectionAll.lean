import QiushiPlane462GenSectionBlock0
import QiushiPlane462GenSectionBlock1
import QiushiPlane462GenSectionBlock2
import QiushiPlane462GenSectionBlock3
import QiushiPlane462GenSectionBlock4
import QiushiPlane462GenSectionBlock5
import QiushiPlane462GenSectionBlock6
import QiushiPlane462GenSectionBlock7
import QiushiPlane462GenSectionBlock8
import QiushiPlane462GenSectionBlock9
import QiushiPlane462GenSectionBlock10
import QiushiPlane462GenSectionBlock11
import QiushiPlane462GenSectionBlock12
import QiushiPlane462GenSectionBlock13
import QiushiPlane462GenSectionBlock14
import QiushiPlane462GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane462GenSectionAll : forall i, plane462GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane462GenSectionBlock0
  | ⟨1, _⟩ => exact plane462GenSectionBlock1
  | ⟨2, _⟩ => exact plane462GenSectionBlock2
  | ⟨3, _⟩ => exact plane462GenSectionBlock3
  | ⟨4, _⟩ => exact plane462GenSectionBlock4
  | ⟨5, _⟩ => exact plane462GenSectionBlock5
  | ⟨6, _⟩ => exact plane462GenSectionBlock6
  | ⟨7, _⟩ => exact plane462GenSectionBlock7
  | ⟨8, _⟩ => exact plane462GenSectionBlock8
  | ⟨9, _⟩ => exact plane462GenSectionBlock9
  | ⟨10, _⟩ => exact plane462GenSectionBlock10
  | ⟨11, _⟩ => exact plane462GenSectionBlock11
  | ⟨12, _⟩ => exact plane462GenSectionBlock12
  | ⟨13, _⟩ => exact plane462GenSectionBlock13
  | ⟨14, _⟩ => exact plane462GenSectionBlock14
  | ⟨15, _⟩ => exact plane462GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
