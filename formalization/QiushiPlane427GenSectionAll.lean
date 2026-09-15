import QiushiPlane427GenSectionBlock0
import QiushiPlane427GenSectionBlock1
import QiushiPlane427GenSectionBlock2
import QiushiPlane427GenSectionBlock3
import QiushiPlane427GenSectionBlock4
import QiushiPlane427GenSectionBlock5
import QiushiPlane427GenSectionBlock6
import QiushiPlane427GenSectionBlock7
import QiushiPlane427GenSectionBlock8
import QiushiPlane427GenSectionBlock9
import QiushiPlane427GenSectionBlock10
import QiushiPlane427GenSectionBlock11
import QiushiPlane427GenSectionBlock12
import QiushiPlane427GenSectionBlock13
import QiushiPlane427GenSectionBlock14
import QiushiPlane427GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane427GenSectionAll : forall i, plane427GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane427GenSectionBlock0
  | ⟨1, _⟩ => exact plane427GenSectionBlock1
  | ⟨2, _⟩ => exact plane427GenSectionBlock2
  | ⟨3, _⟩ => exact plane427GenSectionBlock3
  | ⟨4, _⟩ => exact plane427GenSectionBlock4
  | ⟨5, _⟩ => exact plane427GenSectionBlock5
  | ⟨6, _⟩ => exact plane427GenSectionBlock6
  | ⟨7, _⟩ => exact plane427GenSectionBlock7
  | ⟨8, _⟩ => exact plane427GenSectionBlock8
  | ⟨9, _⟩ => exact plane427GenSectionBlock9
  | ⟨10, _⟩ => exact plane427GenSectionBlock10
  | ⟨11, _⟩ => exact plane427GenSectionBlock11
  | ⟨12, _⟩ => exact plane427GenSectionBlock12
  | ⟨13, _⟩ => exact plane427GenSectionBlock13
  | ⟨14, _⟩ => exact plane427GenSectionBlock14
  | ⟨15, _⟩ => exact plane427GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
