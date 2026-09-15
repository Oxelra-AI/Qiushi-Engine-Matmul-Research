import QiushiPlane453GenSourceBlock0
import QiushiPlane453GenSourceBlock1
import QiushiPlane453GenSourceBlock2
import QiushiPlane453GenSourceBlock3
import QiushiPlane453GenSourceBlock4
import QiushiPlane453GenSourceBlock5
import QiushiPlane453GenSourceBlock6
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane453GenSourceAll : forall i, plane453GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 7) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane453GenSourceBlock0
  | ⟨1, _⟩ => exact plane453GenSourceBlock1
  | ⟨2, _⟩ => exact plane453GenSourceBlock2
  | ⟨3, _⟩ => exact plane453GenSourceBlock3
  | ⟨4, _⟩ => exact plane453GenSourceBlock4
  | ⟨5, _⟩ => exact plane453GenSourceBlock5
  | ⟨6, _⟩ => exact plane453GenSourceBlock6
  | ⟨k + 7, h⟩ => omega
end QiushiMatmul
