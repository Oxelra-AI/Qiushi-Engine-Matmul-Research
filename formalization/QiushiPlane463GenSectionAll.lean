import QiushiPlane463GenSectionBlock0
import QiushiPlane463GenSectionBlock1
import QiushiPlane463GenSectionBlock2
import QiushiPlane463GenSectionBlock3
import QiushiPlane463GenSectionBlock4
import QiushiPlane463GenSectionBlock5
import QiushiPlane463GenSectionBlock6
import QiushiPlane463GenSectionBlock7
import QiushiPlane463GenSectionBlock8
import QiushiPlane463GenSectionBlock9
import QiushiPlane463GenSectionBlock10
import QiushiPlane463GenSectionBlock11
import QiushiPlane463GenSectionBlock12
import QiushiPlane463GenSectionBlock13
import QiushiPlane463GenSectionBlock14
import QiushiPlane463GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane463GenSectionAll : forall i, plane463GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane463GenSectionBlock0
  | ⟨1, _⟩ => exact plane463GenSectionBlock1
  | ⟨2, _⟩ => exact plane463GenSectionBlock2
  | ⟨3, _⟩ => exact plane463GenSectionBlock3
  | ⟨4, _⟩ => exact plane463GenSectionBlock4
  | ⟨5, _⟩ => exact plane463GenSectionBlock5
  | ⟨6, _⟩ => exact plane463GenSectionBlock6
  | ⟨7, _⟩ => exact plane463GenSectionBlock7
  | ⟨8, _⟩ => exact plane463GenSectionBlock8
  | ⟨9, _⟩ => exact plane463GenSectionBlock9
  | ⟨10, _⟩ => exact plane463GenSectionBlock10
  | ⟨11, _⟩ => exact plane463GenSectionBlock11
  | ⟨12, _⟩ => exact plane463GenSectionBlock12
  | ⟨13, _⟩ => exact plane463GenSectionBlock13
  | ⟨14, _⟩ => exact plane463GenSectionBlock14
  | ⟨15, _⟩ => exact plane463GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
