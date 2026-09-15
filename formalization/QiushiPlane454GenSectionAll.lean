import QiushiPlane454GenSectionBlock0
import QiushiPlane454GenSectionBlock1
import QiushiPlane454GenSectionBlock2
import QiushiPlane454GenSectionBlock3
import QiushiPlane454GenSectionBlock4
import QiushiPlane454GenSectionBlock5
import QiushiPlane454GenSectionBlock6
import QiushiPlane454GenSectionBlock7
import QiushiPlane454GenSectionBlock8
import QiushiPlane454GenSectionBlock9
import QiushiPlane454GenSectionBlock10
import QiushiPlane454GenSectionBlock11
import QiushiPlane454GenSectionBlock12
import QiushiPlane454GenSectionBlock13
import QiushiPlane454GenSectionBlock14
import QiushiPlane454GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane454GenSectionAll : forall i, plane454GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane454GenSectionBlock0
  | ⟨1, _⟩ => exact plane454GenSectionBlock1
  | ⟨2, _⟩ => exact plane454GenSectionBlock2
  | ⟨3, _⟩ => exact plane454GenSectionBlock3
  | ⟨4, _⟩ => exact plane454GenSectionBlock4
  | ⟨5, _⟩ => exact plane454GenSectionBlock5
  | ⟨6, _⟩ => exact plane454GenSectionBlock6
  | ⟨7, _⟩ => exact plane454GenSectionBlock7
  | ⟨8, _⟩ => exact plane454GenSectionBlock8
  | ⟨9, _⟩ => exact plane454GenSectionBlock9
  | ⟨10, _⟩ => exact plane454GenSectionBlock10
  | ⟨11, _⟩ => exact plane454GenSectionBlock11
  | ⟨12, _⟩ => exact plane454GenSectionBlock12
  | ⟨13, _⟩ => exact plane454GenSectionBlock13
  | ⟨14, _⟩ => exact plane454GenSectionBlock14
  | ⟨15, _⟩ => exact plane454GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
