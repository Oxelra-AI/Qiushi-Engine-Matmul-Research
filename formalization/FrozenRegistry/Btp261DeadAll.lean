import FrozenRegistry.Btp261DeadBlock0
import FrozenRegistry.Btp261DeadBlock1
import FrozenRegistry.Btp261DeadBlock2
import FrozenRegistry.Btp261DeadBlock3
import FrozenRegistry.Btp261DeadBlock4
import FrozenRegistry.Btp261DeadBlock5
import FrozenRegistry.Btp261DeadBlock6
import FrozenRegistry.Btp261DeadBlock7
import FrozenRegistry.Btp261DeadBlock8
import FrozenRegistry.Btp261DeadBlock9
import FrozenRegistry.Btp261DeadBlock10
import FrozenRegistry.Btp261DeadBlock11
import FrozenRegistry.Btp261DeadBlock12
import FrozenRegistry.Btp261DeadBlock13
import FrozenRegistry.Btp261DeadBlock14
import FrozenRegistry.Btp261DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane261BtpGenDeadAll : forall i, plane261BtpGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane261BtpGenDeadBlock0
  | ⟨1, _⟩ => exact plane261BtpGenDeadBlock1
  | ⟨2, _⟩ => exact plane261BtpGenDeadBlock2
  | ⟨3, _⟩ => exact plane261BtpGenDeadBlock3
  | ⟨4, _⟩ => exact plane261BtpGenDeadBlock4
  | ⟨5, _⟩ => exact plane261BtpGenDeadBlock5
  | ⟨6, _⟩ => exact plane261BtpGenDeadBlock6
  | ⟨7, _⟩ => exact plane261BtpGenDeadBlock7
  | ⟨8, _⟩ => exact plane261BtpGenDeadBlock8
  | ⟨9, _⟩ => exact plane261BtpGenDeadBlock9
  | ⟨10, _⟩ => exact plane261BtpGenDeadBlock10
  | ⟨11, _⟩ => exact plane261BtpGenDeadBlock11
  | ⟨12, _⟩ => exact plane261BtpGenDeadBlock12
  | ⟨13, _⟩ => exact plane261BtpGenDeadBlock13
  | ⟨14, _⟩ => exact plane261BtpGenDeadBlock14
  | ⟨15, _⟩ => exact plane261BtpGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
