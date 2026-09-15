import QiushiPlane483GenDeadBlock0
import QiushiPlane483GenDeadBlock1
import QiushiPlane483GenDeadBlock2
import QiushiPlane483GenDeadBlock3
import QiushiPlane483GenDeadBlock4
import QiushiPlane483GenDeadBlock5
import QiushiPlane483GenDeadBlock6
import QiushiPlane483GenDeadBlock7
import QiushiPlane483GenDeadBlock8
import QiushiPlane483GenDeadBlock9
import QiushiPlane483GenDeadBlock10
import QiushiPlane483GenDeadBlock11
import QiushiPlane483GenDeadBlock12
import QiushiPlane483GenDeadBlock13
import QiushiPlane483GenDeadBlock14
import QiushiPlane483GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane483GenDeadAll : forall i, plane483GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane483GenDeadBlock0
  | ⟨1, _⟩ => exact plane483GenDeadBlock1
  | ⟨2, _⟩ => exact plane483GenDeadBlock2
  | ⟨3, _⟩ => exact plane483GenDeadBlock3
  | ⟨4, _⟩ => exact plane483GenDeadBlock4
  | ⟨5, _⟩ => exact plane483GenDeadBlock5
  | ⟨6, _⟩ => exact plane483GenDeadBlock6
  | ⟨7, _⟩ => exact plane483GenDeadBlock7
  | ⟨8, _⟩ => exact plane483GenDeadBlock8
  | ⟨9, _⟩ => exact plane483GenDeadBlock9
  | ⟨10, _⟩ => exact plane483GenDeadBlock10
  | ⟨11, _⟩ => exact plane483GenDeadBlock11
  | ⟨12, _⟩ => exact plane483GenDeadBlock12
  | ⟨13, _⟩ => exact plane483GenDeadBlock13
  | ⟨14, _⟩ => exact plane483GenDeadBlock14
  | ⟨15, _⟩ => exact plane483GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
