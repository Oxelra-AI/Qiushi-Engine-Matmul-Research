import FrozenRegistry.Btp224DeadBlock0
import FrozenRegistry.Btp224DeadBlock1
import FrozenRegistry.Btp224DeadBlock2
import FrozenRegistry.Btp224DeadBlock3
import FrozenRegistry.Btp224DeadBlock4
import FrozenRegistry.Btp224DeadBlock5
import FrozenRegistry.Btp224DeadBlock6
import FrozenRegistry.Btp224DeadBlock7
import FrozenRegistry.Btp224DeadBlock8
import FrozenRegistry.Btp224DeadBlock9
import FrozenRegistry.Btp224DeadBlock10
import FrozenRegistry.Btp224DeadBlock11
import FrozenRegistry.Btp224DeadBlock12
import FrozenRegistry.Btp224DeadBlock13
import FrozenRegistry.Btp224DeadBlock14
import FrozenRegistry.Btp224DeadBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane224BtpGenDeadAll : forall i, plane224BtpGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane224BtpGenDeadBlock0
  | ⟨1, _⟩ => exact plane224BtpGenDeadBlock1
  | ⟨2, _⟩ => exact plane224BtpGenDeadBlock2
  | ⟨3, _⟩ => exact plane224BtpGenDeadBlock3
  | ⟨4, _⟩ => exact plane224BtpGenDeadBlock4
  | ⟨5, _⟩ => exact plane224BtpGenDeadBlock5
  | ⟨6, _⟩ => exact plane224BtpGenDeadBlock6
  | ⟨7, _⟩ => exact plane224BtpGenDeadBlock7
  | ⟨8, _⟩ => exact plane224BtpGenDeadBlock8
  | ⟨9, _⟩ => exact plane224BtpGenDeadBlock9
  | ⟨10, _⟩ => exact plane224BtpGenDeadBlock10
  | ⟨11, _⟩ => exact plane224BtpGenDeadBlock11
  | ⟨12, _⟩ => exact plane224BtpGenDeadBlock12
  | ⟨13, _⟩ => exact plane224BtpGenDeadBlock13
  | ⟨14, _⟩ => exact plane224BtpGenDeadBlock14
  | ⟨15, _⟩ => exact plane224BtpGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
