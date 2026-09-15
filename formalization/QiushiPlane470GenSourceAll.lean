import QiushiPlane470GenSourceBlock0
import QiushiPlane470GenSourceBlock1
import QiushiPlane470GenSourceBlock2
import QiushiPlane470GenSourceBlock3
import QiushiPlane470GenSourceBlock4
import QiushiPlane470GenSourceBlock5
import QiushiPlane470GenSourceBlock6
import QiushiPlane470GenSourceBlock7
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane470GenSourceAll : forall i, plane470GenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 8) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane470GenSourceBlock0
  | ⟨1, _⟩ => exact plane470GenSourceBlock1
  | ⟨2, _⟩ => exact plane470GenSourceBlock2
  | ⟨3, _⟩ => exact plane470GenSourceBlock3
  | ⟨4, _⟩ => exact plane470GenSourceBlock4
  | ⟨5, _⟩ => exact plane470GenSourceBlock5
  | ⟨6, _⟩ => exact plane470GenSourceBlock6
  | ⟨7, _⟩ => exact plane470GenSourceBlock7
  | ⟨k + 8, h⟩ => omega
end QiushiMatmul
