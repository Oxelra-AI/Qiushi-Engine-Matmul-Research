import QiushiPlane429GenSectionBlock0
import QiushiPlane429GenSectionBlock1
import QiushiPlane429GenSectionBlock2
import QiushiPlane429GenSectionBlock3
import QiushiPlane429GenSectionBlock4
import QiushiPlane429GenSectionBlock5
import QiushiPlane429GenSectionBlock6
import QiushiPlane429GenSectionBlock7
import QiushiPlane429GenSectionBlock8
import QiushiPlane429GenSectionBlock9
import QiushiPlane429GenSectionBlock10
import QiushiPlane429GenSectionBlock11
import QiushiPlane429GenSectionBlock12
import QiushiPlane429GenSectionBlock13
import QiushiPlane429GenSectionBlock14
import QiushiPlane429GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane429GenSectionAll : forall i, plane429GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane429GenSectionBlock0
  | ⟨1, _⟩ => exact plane429GenSectionBlock1
  | ⟨2, _⟩ => exact plane429GenSectionBlock2
  | ⟨3, _⟩ => exact plane429GenSectionBlock3
  | ⟨4, _⟩ => exact plane429GenSectionBlock4
  | ⟨5, _⟩ => exact plane429GenSectionBlock5
  | ⟨6, _⟩ => exact plane429GenSectionBlock6
  | ⟨7, _⟩ => exact plane429GenSectionBlock7
  | ⟨8, _⟩ => exact plane429GenSectionBlock8
  | ⟨9, _⟩ => exact plane429GenSectionBlock9
  | ⟨10, _⟩ => exact plane429GenSectionBlock10
  | ⟨11, _⟩ => exact plane429GenSectionBlock11
  | ⟨12, _⟩ => exact plane429GenSectionBlock12
  | ⟨13, _⟩ => exact plane429GenSectionBlock13
  | ⟨14, _⟩ => exact plane429GenSectionBlock14
  | ⟨15, _⟩ => exact plane429GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
