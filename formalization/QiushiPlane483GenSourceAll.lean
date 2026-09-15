import QiushiPlane483GenSourceBlock0
import QiushiPlane483GenSourceBlock1
import QiushiPlane483GenSourceBlock2
import QiushiPlane483GenSourceBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane483GenSourceAll : forall i, plane483GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane483GenSourceBlock0
  | ⟨1, _⟩ => exact plane483GenSourceBlock1
  | ⟨2, _⟩ => exact plane483GenSourceBlock2
  | ⟨3, _⟩ => exact plane483GenSourceBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
