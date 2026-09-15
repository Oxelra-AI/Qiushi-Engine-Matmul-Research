import FrozenRegistry.Btp287SourceBlock0
import FrozenRegistry.Btp287SourceBlock1
import FrozenRegistry.Btp287SourceBlock2
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane287BtpGenSourceAll : forall i, plane287BtpGenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 3) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane287BtpGenSourceBlock0
  | ⟨1, _⟩ => exact plane287BtpGenSourceBlock1
  | ⟨2, _⟩ => exact plane287BtpGenSourceBlock2
  | ⟨k + 3, h⟩ => omega
end QiushiMatmul
