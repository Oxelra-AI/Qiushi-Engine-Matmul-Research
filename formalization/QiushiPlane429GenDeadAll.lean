import QiushiPlane429GenDeadBlock0
import QiushiPlane429GenDeadBlock1
import QiushiPlane429GenDeadBlock2
import QiushiPlane429GenDeadBlock3
import QiushiPlane429GenDeadBlock4
import QiushiPlane429GenDeadBlock5
import QiushiPlane429GenDeadBlock6
import QiushiPlane429GenDeadBlock7
import QiushiPlane429GenDeadBlock8
import QiushiPlane429GenDeadBlock9
import QiushiPlane429GenDeadBlock10
import QiushiPlane429GenDeadBlock11
import QiushiPlane429GenDeadBlock12
import QiushiPlane429GenDeadBlock13
import QiushiPlane429GenDeadBlock14
import QiushiPlane429GenDeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane429GenDeadAll : forall i, plane429GenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane429GenDeadBlock0
  | ⟨1, _⟩ => exact plane429GenDeadBlock1
  | ⟨2, _⟩ => exact plane429GenDeadBlock2
  | ⟨3, _⟩ => exact plane429GenDeadBlock3
  | ⟨4, _⟩ => exact plane429GenDeadBlock4
  | ⟨5, _⟩ => exact plane429GenDeadBlock5
  | ⟨6, _⟩ => exact plane429GenDeadBlock6
  | ⟨7, _⟩ => exact plane429GenDeadBlock7
  | ⟨8, _⟩ => exact plane429GenDeadBlock8
  | ⟨9, _⟩ => exact plane429GenDeadBlock9
  | ⟨10, _⟩ => exact plane429GenDeadBlock10
  | ⟨11, _⟩ => exact plane429GenDeadBlock11
  | ⟨12, _⟩ => exact plane429GenDeadBlock12
  | ⟨13, _⟩ => exact plane429GenDeadBlock13
  | ⟨14, _⟩ => exact plane429GenDeadBlock14
  | ⟨15, _⟩ => exact plane429GenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
