import QiushiGlobalOrbitUnused399DeadBlock0
import QiushiGlobalOrbitUnused399DeadBlock1
import QiushiGlobalOrbitUnused399DeadBlock2
import QiushiGlobalOrbitUnused399DeadBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane399UnusedGenDeadAll : forall i, plane399UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane399UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane399UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane399UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane399UnusedGenDeadBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
