import QiushiPlane292GenSectionBlock0
import QiushiPlane292GenSectionBlock1
import QiushiPlane292GenSectionBlock2
import QiushiPlane292GenSectionBlock3
import QiushiPlane292GenSectionBlock4
import QiushiPlane292GenSectionBlock5
import QiushiPlane292GenSectionBlock6
import QiushiPlane292GenSectionBlock7
import QiushiPlane292GenSectionBlock8
import QiushiPlane292GenSectionBlock9
import QiushiPlane292GenSectionBlock10
import QiushiPlane292GenSectionBlock11
import QiushiPlane292GenSectionBlock12
import QiushiPlane292GenSectionBlock13
import QiushiPlane292GenSectionBlock14
import QiushiPlane292GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane292GenSectionAll : forall i, plane292GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane292GenSectionBlock0
  | ⟨1, _⟩ => exact plane292GenSectionBlock1
  | ⟨2, _⟩ => exact plane292GenSectionBlock2
  | ⟨3, _⟩ => exact plane292GenSectionBlock3
  | ⟨4, _⟩ => exact plane292GenSectionBlock4
  | ⟨5, _⟩ => exact plane292GenSectionBlock5
  | ⟨6, _⟩ => exact plane292GenSectionBlock6
  | ⟨7, _⟩ => exact plane292GenSectionBlock7
  | ⟨8, _⟩ => exact plane292GenSectionBlock8
  | ⟨9, _⟩ => exact plane292GenSectionBlock9
  | ⟨10, _⟩ => exact plane292GenSectionBlock10
  | ⟨11, _⟩ => exact plane292GenSectionBlock11
  | ⟨12, _⟩ => exact plane292GenSectionBlock12
  | ⟨13, _⟩ => exact plane292GenSectionBlock13
  | ⟨14, _⟩ => exact plane292GenSectionBlock14
  | ⟨15, _⟩ => exact plane292GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
