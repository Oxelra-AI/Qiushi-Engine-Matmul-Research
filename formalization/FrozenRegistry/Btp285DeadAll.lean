import FrozenRegistry.Btp285DeadBlock0
import FrozenRegistry.Btp285DeadBlock1
import FrozenRegistry.Btp285DeadBlock2
import FrozenRegistry.Btp285DeadBlock3
import FrozenRegistry.Btp285DeadBlock4
import FrozenRegistry.Btp285DeadBlock5
import FrozenRegistry.Btp285DeadBlock6
import FrozenRegistry.Btp285DeadBlock7
import FrozenRegistry.Btp285DeadBlock8
import FrozenRegistry.Btp285DeadBlock9
import FrozenRegistry.Btp285DeadBlock10
import FrozenRegistry.Btp285DeadBlock11
import FrozenRegistry.Btp285DeadBlock12
import FrozenRegistry.Btp285DeadBlock13
import FrozenRegistry.Btp285DeadBlock14
import FrozenRegistry.Btp285DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane285BtpGenDeadAll : forall i, plane285BtpGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane285BtpGenDeadBlock0
  | ⟨1, _⟩ => exact plane285BtpGenDeadBlock1
  | ⟨2, _⟩ => exact plane285BtpGenDeadBlock2
  | ⟨3, _⟩ => exact plane285BtpGenDeadBlock3
  | ⟨4, _⟩ => exact plane285BtpGenDeadBlock4
  | ⟨5, _⟩ => exact plane285BtpGenDeadBlock5
  | ⟨6, _⟩ => exact plane285BtpGenDeadBlock6
  | ⟨7, _⟩ => exact plane285BtpGenDeadBlock7
  | ⟨8, _⟩ => exact plane285BtpGenDeadBlock8
  | ⟨9, _⟩ => exact plane285BtpGenDeadBlock9
  | ⟨10, _⟩ => exact plane285BtpGenDeadBlock10
  | ⟨11, _⟩ => exact plane285BtpGenDeadBlock11
  | ⟨12, _⟩ => exact plane285BtpGenDeadBlock12
  | ⟨13, _⟩ => exact plane285BtpGenDeadBlock13
  | ⟨14, _⟩ => exact plane285BtpGenDeadBlock14
  | ⟨15, _⟩ => exact plane285BtpGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
