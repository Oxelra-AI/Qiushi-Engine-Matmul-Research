import FrozenRegistry.Btp263DeadBlock0
import FrozenRegistry.Btp263DeadBlock1
import FrozenRegistry.Btp263DeadBlock2
import FrozenRegistry.Btp263DeadBlock3
import FrozenRegistry.Btp263DeadBlock4
import FrozenRegistry.Btp263DeadBlock5
import FrozenRegistry.Btp263DeadBlock6
import FrozenRegistry.Btp263DeadBlock7
import FrozenRegistry.Btp263DeadBlock8
import FrozenRegistry.Btp263DeadBlock9
import FrozenRegistry.Btp263DeadBlock10
import FrozenRegistry.Btp263DeadBlock11
import FrozenRegistry.Btp263DeadBlock12
import FrozenRegistry.Btp263DeadBlock13
import FrozenRegistry.Btp263DeadBlock14
import FrozenRegistry.Btp263DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane263BtpGenDeadAll : forall i, plane263BtpGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane263BtpGenDeadBlock0
  | ⟨1, _⟩ => exact plane263BtpGenDeadBlock1
  | ⟨2, _⟩ => exact plane263BtpGenDeadBlock2
  | ⟨3, _⟩ => exact plane263BtpGenDeadBlock3
  | ⟨4, _⟩ => exact plane263BtpGenDeadBlock4
  | ⟨5, _⟩ => exact plane263BtpGenDeadBlock5
  | ⟨6, _⟩ => exact plane263BtpGenDeadBlock6
  | ⟨7, _⟩ => exact plane263BtpGenDeadBlock7
  | ⟨8, _⟩ => exact plane263BtpGenDeadBlock8
  | ⟨9, _⟩ => exact plane263BtpGenDeadBlock9
  | ⟨10, _⟩ => exact plane263BtpGenDeadBlock10
  | ⟨11, _⟩ => exact plane263BtpGenDeadBlock11
  | ⟨12, _⟩ => exact plane263BtpGenDeadBlock12
  | ⟨13, _⟩ => exact plane263BtpGenDeadBlock13
  | ⟨14, _⟩ => exact plane263BtpGenDeadBlock14
  | ⟨15, _⟩ => exact plane263BtpGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
