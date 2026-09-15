import QiushiPlane472GenSectionBlock0
import QiushiPlane472GenSectionBlock1
import QiushiPlane472GenSectionBlock2
import QiushiPlane472GenSectionBlock3
import QiushiPlane472GenSectionBlock4
import QiushiPlane472GenSectionBlock5
import QiushiPlane472GenSectionBlock6
import QiushiPlane472GenSectionBlock7
import QiushiPlane472GenSectionBlock8
import QiushiPlane472GenSectionBlock9
import QiushiPlane472GenSectionBlock10
import QiushiPlane472GenSectionBlock11
import QiushiPlane472GenSectionBlock12
import QiushiPlane472GenSectionBlock13
import QiushiPlane472GenSectionBlock14
import QiushiPlane472GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane472GenSectionAll : forall i, plane472GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane472GenSectionBlock0
  | ⟨1, _⟩ => exact plane472GenSectionBlock1
  | ⟨2, _⟩ => exact plane472GenSectionBlock2
  | ⟨3, _⟩ => exact plane472GenSectionBlock3
  | ⟨4, _⟩ => exact plane472GenSectionBlock4
  | ⟨5, _⟩ => exact plane472GenSectionBlock5
  | ⟨6, _⟩ => exact plane472GenSectionBlock6
  | ⟨7, _⟩ => exact plane472GenSectionBlock7
  | ⟨8, _⟩ => exact plane472GenSectionBlock8
  | ⟨9, _⟩ => exact plane472GenSectionBlock9
  | ⟨10, _⟩ => exact plane472GenSectionBlock10
  | ⟨11, _⟩ => exact plane472GenSectionBlock11
  | ⟨12, _⟩ => exact plane472GenSectionBlock12
  | ⟨13, _⟩ => exact plane472GenSectionBlock13
  | ⟨14, _⟩ => exact plane472GenSectionBlock14
  | ⟨15, _⟩ => exact plane472GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
