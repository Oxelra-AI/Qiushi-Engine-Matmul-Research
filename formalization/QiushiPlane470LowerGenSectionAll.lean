import QiushiPlane470LowerGenSectionBlock0
import QiushiPlane470LowerGenSectionBlock1
import QiushiPlane470LowerGenSectionBlock2
import QiushiPlane470LowerGenSectionBlock3
import QiushiPlane470LowerGenSectionBlock4
import QiushiPlane470LowerGenSectionBlock5
import QiushiPlane470LowerGenSectionBlock6
import QiushiPlane470LowerGenSectionBlock7
import QiushiPlane470LowerGenSectionBlock8
import QiushiPlane470LowerGenSectionBlock9
import QiushiPlane470LowerGenSectionBlock10
import QiushiPlane470LowerGenSectionBlock11
import QiushiPlane470LowerGenSectionBlock12
import QiushiPlane470LowerGenSectionBlock13
import QiushiPlane470LowerGenSectionBlock14
import QiushiPlane470LowerGenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane470LowerGenSectionAll : forall i, plane470LowerGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane470LowerGenSectionBlock0
  | ⟨1, _⟩ => exact plane470LowerGenSectionBlock1
  | ⟨2, _⟩ => exact plane470LowerGenSectionBlock2
  | ⟨3, _⟩ => exact plane470LowerGenSectionBlock3
  | ⟨4, _⟩ => exact plane470LowerGenSectionBlock4
  | ⟨5, _⟩ => exact plane470LowerGenSectionBlock5
  | ⟨6, _⟩ => exact plane470LowerGenSectionBlock6
  | ⟨7, _⟩ => exact plane470LowerGenSectionBlock7
  | ⟨8, _⟩ => exact plane470LowerGenSectionBlock8
  | ⟨9, _⟩ => exact plane470LowerGenSectionBlock9
  | ⟨10, _⟩ => exact plane470LowerGenSectionBlock10
  | ⟨11, _⟩ => exact plane470LowerGenSectionBlock11
  | ⟨12, _⟩ => exact plane470LowerGenSectionBlock12
  | ⟨13, _⟩ => exact plane470LowerGenSectionBlock13
  | ⟨14, _⟩ => exact plane470LowerGenSectionBlock14
  | ⟨15, _⟩ => exact plane470LowerGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
