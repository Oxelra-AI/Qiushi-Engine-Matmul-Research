import QiushiGlobalOrbitUnused402DeadBlock0
import QiushiGlobalOrbitUnused402DeadBlock1
import QiushiGlobalOrbitUnused402DeadBlock2
import QiushiGlobalOrbitUnused402DeadBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane402UnusedGenDeadAll : forall i, plane402UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane402UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane402UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane402UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane402UnusedGenDeadBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
