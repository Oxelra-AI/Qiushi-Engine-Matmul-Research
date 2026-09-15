import QiushiGlobalOrbitUnused408DeadBlock0
import QiushiGlobalOrbitUnused408DeadBlock1
import QiushiGlobalOrbitUnused408DeadBlock2
import QiushiGlobalOrbitUnused408DeadBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane408UnusedGenDeadAll : forall i, plane408UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane408UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane408UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane408UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane408UnusedGenDeadBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
