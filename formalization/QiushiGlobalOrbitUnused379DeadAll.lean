import QiushiGlobalOrbitUnused379DeadBlock0
import QiushiGlobalOrbitUnused379DeadBlock1
import QiushiGlobalOrbitUnused379DeadBlock2
import QiushiGlobalOrbitUnused379DeadBlock3
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane379UnusedGenDeadAll : forall i, plane379UnusedGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 4) (width := 128)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane379UnusedGenDeadBlock0
  | ⟨1, _⟩ => exact plane379UnusedGenDeadBlock1
  | ⟨2, _⟩ => exact plane379UnusedGenDeadBlock2
  | ⟨3, _⟩ => exact plane379UnusedGenDeadBlock3
  | ⟨k + 4, h⟩ => omega
end QiushiMatmul
