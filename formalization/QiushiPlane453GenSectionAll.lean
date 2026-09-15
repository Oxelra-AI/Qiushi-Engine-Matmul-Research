import QiushiPlane453GenSectionBlock0
import QiushiPlane453GenSectionBlock1
import QiushiPlane453GenSectionBlock2
import QiushiPlane453GenSectionBlock3
import QiushiPlane453GenSectionBlock4
import QiushiPlane453GenSectionBlock5
import QiushiPlane453GenSectionBlock6
import QiushiPlane453GenSectionBlock7
import QiushiPlane453GenSectionBlock8
import QiushiPlane453GenSectionBlock9
import QiushiPlane453GenSectionBlock10
import QiushiPlane453GenSectionBlock11
import QiushiPlane453GenSectionBlock12
import QiushiPlane453GenSectionBlock13
import QiushiPlane453GenSectionBlock14
import QiushiPlane453GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane453GenSectionAll : forall i, plane453GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane453GenSectionBlock0
  | ⟨1, _⟩ => exact plane453GenSectionBlock1
  | ⟨2, _⟩ => exact plane453GenSectionBlock2
  | ⟨3, _⟩ => exact plane453GenSectionBlock3
  | ⟨4, _⟩ => exact plane453GenSectionBlock4
  | ⟨5, _⟩ => exact plane453GenSectionBlock5
  | ⟨6, _⟩ => exact plane453GenSectionBlock6
  | ⟨7, _⟩ => exact plane453GenSectionBlock7
  | ⟨8, _⟩ => exact plane453GenSectionBlock8
  | ⟨9, _⟩ => exact plane453GenSectionBlock9
  | ⟨10, _⟩ => exact plane453GenSectionBlock10
  | ⟨11, _⟩ => exact plane453GenSectionBlock11
  | ⟨12, _⟩ => exact plane453GenSectionBlock12
  | ⟨13, _⟩ => exact plane453GenSectionBlock13
  | ⟨14, _⟩ => exact plane453GenSectionBlock14
  | ⟨15, _⟩ => exact plane453GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
