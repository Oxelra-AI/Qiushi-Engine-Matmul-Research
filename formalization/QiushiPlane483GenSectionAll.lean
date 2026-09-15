import QiushiPlane483GenSectionBlock0
import QiushiPlane483GenSectionBlock1
import QiushiPlane483GenSectionBlock2
import QiushiPlane483GenSectionBlock3
import QiushiPlane483GenSectionBlock4
import QiushiPlane483GenSectionBlock5
import QiushiPlane483GenSectionBlock6
import QiushiPlane483GenSectionBlock7
import QiushiPlane483GenSectionBlock8
import QiushiPlane483GenSectionBlock9
import QiushiPlane483GenSectionBlock10
import QiushiPlane483GenSectionBlock11
import QiushiPlane483GenSectionBlock12
import QiushiPlane483GenSectionBlock13
import QiushiPlane483GenSectionBlock14
import QiushiPlane483GenSectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane483GenSectionAll : forall i, plane483GenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane483GenSectionBlock0
  | ⟨1, _⟩ => exact plane483GenSectionBlock1
  | ⟨2, _⟩ => exact plane483GenSectionBlock2
  | ⟨3, _⟩ => exact plane483GenSectionBlock3
  | ⟨4, _⟩ => exact plane483GenSectionBlock4
  | ⟨5, _⟩ => exact plane483GenSectionBlock5
  | ⟨6, _⟩ => exact plane483GenSectionBlock6
  | ⟨7, _⟩ => exact plane483GenSectionBlock7
  | ⟨8, _⟩ => exact plane483GenSectionBlock8
  | ⟨9, _⟩ => exact plane483GenSectionBlock9
  | ⟨10, _⟩ => exact plane483GenSectionBlock10
  | ⟨11, _⟩ => exact plane483GenSectionBlock11
  | ⟨12, _⟩ => exact plane483GenSectionBlock12
  | ⟨13, _⟩ => exact plane483GenSectionBlock13
  | ⟨14, _⟩ => exact plane483GenSectionBlock14
  | ⟨15, _⟩ => exact plane483GenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
