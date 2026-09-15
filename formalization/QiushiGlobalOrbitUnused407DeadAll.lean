import QiushiGlobalOrbitUnused407DeadBlock0
import QiushiGlobalOrbitUnused407DeadBlock1
import QiushiGlobalOrbitUnused407DeadBlock2
import QiushiGlobalOrbitUnused407DeadBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane407UnusedGenDeadAll : forall i, plane407UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane407UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane407UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane407UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane407UnusedGenDeadBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
