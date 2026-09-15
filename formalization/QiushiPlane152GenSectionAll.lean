import QiushiPlane152GenSectionBlock0
import QiushiPlane152GenSectionBlock1
import QiushiPlane152GenSectionBlock2
import QiushiPlane152GenSectionBlock3
import QiushiPlane152GenSectionBlock4
import QiushiPlane152GenSectionBlock5
import QiushiPlane152GenSectionBlock6
import QiushiPlane152GenSectionBlock7
import QiushiPlane152GenSectionBlock8
import QiushiPlane152GenSectionBlock9
import QiushiPlane152GenSectionBlock10
import QiushiPlane152GenSectionBlock11
import QiushiPlane152GenSectionBlock12
import QiushiPlane152GenSectionBlock13
import QiushiPlane152GenSectionBlock14
import QiushiPlane152GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane152GenSectionAll : forall i, plane152GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane152GenSectionBlock0
  | ⟨1, _⟩ => exact plane152GenSectionBlock1
  | ⟨2, _⟩ => exact plane152GenSectionBlock2
  | ⟨3, _⟩ => exact plane152GenSectionBlock3
  | ⟨4, _⟩ => exact plane152GenSectionBlock4
  | ⟨5, _⟩ => exact plane152GenSectionBlock5
  | ⟨6, _⟩ => exact plane152GenSectionBlock6
  | ⟨7, _⟩ => exact plane152GenSectionBlock7
  | ⟨8, _⟩ => exact plane152GenSectionBlock8
  | ⟨9, _⟩ => exact plane152GenSectionBlock9
  | ⟨10, _⟩ => exact plane152GenSectionBlock10
  | ⟨11, _⟩ => exact plane152GenSectionBlock11
  | ⟨12, _⟩ => exact plane152GenSectionBlock12
  | ⟨13, _⟩ => exact plane152GenSectionBlock13
  | ⟨14, _⟩ => exact plane152GenSectionBlock14
  | ⟨15, _⟩ => exact plane152GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
