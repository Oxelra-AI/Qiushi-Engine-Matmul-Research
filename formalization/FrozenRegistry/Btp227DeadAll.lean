import FrozenRegistry.Btp227DeadBlock0
import FrozenRegistry.Btp227DeadBlock1
import FrozenRegistry.Btp227DeadBlock2
import FrozenRegistry.Btp227DeadBlock3
import FrozenRegistry.Btp227DeadBlock4
import FrozenRegistry.Btp227DeadBlock5
import FrozenRegistry.Btp227DeadBlock6
import FrozenRegistry.Btp227DeadBlock7
import FrozenRegistry.Btp227DeadBlock8
import FrozenRegistry.Btp227DeadBlock9
import FrozenRegistry.Btp227DeadBlock10
import FrozenRegistry.Btp227DeadBlock11
import FrozenRegistry.Btp227DeadBlock12
import FrozenRegistry.Btp227DeadBlock13
import FrozenRegistry.Btp227DeadBlock14
import FrozenRegistry.Btp227DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane227BtpGenDeadAll : forall i, plane227BtpGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane227BtpGenDeadBlock0
  | ⟨1, _⟩ => exact plane227BtpGenDeadBlock1
  | ⟨2, _⟩ => exact plane227BtpGenDeadBlock2
  | ⟨3, _⟩ => exact plane227BtpGenDeadBlock3
  | ⟨4, _⟩ => exact plane227BtpGenDeadBlock4
  | ⟨5, _⟩ => exact plane227BtpGenDeadBlock5
  | ⟨6, _⟩ => exact plane227BtpGenDeadBlock6
  | ⟨7, _⟩ => exact plane227BtpGenDeadBlock7
  | ⟨8, _⟩ => exact plane227BtpGenDeadBlock8
  | ⟨9, _⟩ => exact plane227BtpGenDeadBlock9
  | ⟨10, _⟩ => exact plane227BtpGenDeadBlock10
  | ⟨11, _⟩ => exact plane227BtpGenDeadBlock11
  | ⟨12, _⟩ => exact plane227BtpGenDeadBlock12
  | ⟨13, _⟩ => exact plane227BtpGenDeadBlock13
  | ⟨14, _⟩ => exact plane227BtpGenDeadBlock14
  | ⟨15, _⟩ => exact plane227BtpGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
