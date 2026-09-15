import QiushiGlobalOrbitUnused383DeadBlock0
import QiushiGlobalOrbitUnused383DeadBlock1
import QiushiGlobalOrbitUnused383DeadBlock2
import QiushiGlobalOrbitUnused383DeadBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane383UnusedGenDeadAll : forall i, plane383UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane383UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane383UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane383UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane383UnusedGenDeadBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
