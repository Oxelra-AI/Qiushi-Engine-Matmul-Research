import QiushiGlobalOrbitUnused382DeadBlock0
import QiushiGlobalOrbitUnused382DeadBlock1
import QiushiGlobalOrbitUnused382DeadBlock2
import QiushiGlobalOrbitUnused382DeadBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane382UnusedGenDeadAll : forall i, plane382UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane382UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane382UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane382UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane382UnusedGenDeadBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
