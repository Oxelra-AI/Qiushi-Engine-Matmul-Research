import FrozenRegistry.Btp287DeadBlock0
import FrozenRegistry.Btp287DeadBlock1
import FrozenRegistry.Btp287DeadBlock2
import FrozenRegistry.Btp287DeadBlock3
import FrozenRegistry.Btp287DeadBlock4
import FrozenRegistry.Btp287DeadBlock5
import FrozenRegistry.Btp287DeadBlock6
import FrozenRegistry.Btp287DeadBlock7
import FrozenRegistry.Btp287DeadBlock8
import FrozenRegistry.Btp287DeadBlock9
import FrozenRegistry.Btp287DeadBlock10
import FrozenRegistry.Btp287DeadBlock11
import FrozenRegistry.Btp287DeadBlock12
import FrozenRegistry.Btp287DeadBlock13
import FrozenRegistry.Btp287DeadBlock14
import FrozenRegistry.Btp287DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane287BtpGenDeadAll : forall i, plane287BtpGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane287BtpGenDeadBlock0
  | ⟨1, _⟩ => exact plane287BtpGenDeadBlock1
  | ⟨2, _⟩ => exact plane287BtpGenDeadBlock2
  | ⟨3, _⟩ => exact plane287BtpGenDeadBlock3
  | ⟨4, _⟩ => exact plane287BtpGenDeadBlock4
  | ⟨5, _⟩ => exact plane287BtpGenDeadBlock5
  | ⟨6, _⟩ => exact plane287BtpGenDeadBlock6
  | ⟨7, _⟩ => exact plane287BtpGenDeadBlock7
  | ⟨8, _⟩ => exact plane287BtpGenDeadBlock8
  | ⟨9, _⟩ => exact plane287BtpGenDeadBlock9
  | ⟨10, _⟩ => exact plane287BtpGenDeadBlock10
  | ⟨11, _⟩ => exact plane287BtpGenDeadBlock11
  | ⟨12, _⟩ => exact plane287BtpGenDeadBlock12
  | ⟨13, _⟩ => exact plane287BtpGenDeadBlock13
  | ⟨14, _⟩ => exact plane287BtpGenDeadBlock14
  | ⟨15, _⟩ => exact plane287BtpGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
