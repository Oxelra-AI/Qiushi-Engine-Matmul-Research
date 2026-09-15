import QiushiGlobalOrbitUnused354DeadBlock0
import QiushiGlobalOrbitUnused354DeadBlock1
import QiushiGlobalOrbitUnused354DeadBlock2
import QiushiGlobalOrbitUnused354DeadBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane354UnusedGenDeadAll : forall i, plane354UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane354UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane354UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane354UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane354UnusedGenDeadBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
