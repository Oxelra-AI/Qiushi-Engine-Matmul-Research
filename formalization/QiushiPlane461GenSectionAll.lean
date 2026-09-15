import QiushiPlane461GenSectionBlock0
import QiushiPlane461GenSectionBlock1
import QiushiPlane461GenSectionBlock2
import QiushiPlane461GenSectionBlock3
import QiushiPlane461GenSectionBlock4
import QiushiPlane461GenSectionBlock5
import QiushiPlane461GenSectionBlock6
import QiushiPlane461GenSectionBlock7
import QiushiPlane461GenSectionBlock8
import QiushiPlane461GenSectionBlock9
import QiushiPlane461GenSectionBlock10
import QiushiPlane461GenSectionBlock11
import QiushiPlane461GenSectionBlock12
import QiushiPlane461GenSectionBlock13
import QiushiPlane461GenSectionBlock14
import QiushiPlane461GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane461GenSectionAll : forall i, plane461GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane461GenSectionBlock0
  | ⟨1, _⟩ => exact plane461GenSectionBlock1
  | ⟨2, _⟩ => exact plane461GenSectionBlock2
  | ⟨3, _⟩ => exact plane461GenSectionBlock3
  | ⟨4, _⟩ => exact plane461GenSectionBlock4
  | ⟨5, _⟩ => exact plane461GenSectionBlock5
  | ⟨6, _⟩ => exact plane461GenSectionBlock6
  | ⟨7, _⟩ => exact plane461GenSectionBlock7
  | ⟨8, _⟩ => exact plane461GenSectionBlock8
  | ⟨9, _⟩ => exact plane461GenSectionBlock9
  | ⟨10, _⟩ => exact plane461GenSectionBlock10
  | ⟨11, _⟩ => exact plane461GenSectionBlock11
  | ⟨12, _⟩ => exact plane461GenSectionBlock12
  | ⟨13, _⟩ => exact plane461GenSectionBlock13
  | ⟨14, _⟩ => exact plane461GenSectionBlock14
  | ⟨15, _⟩ => exact plane461GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
