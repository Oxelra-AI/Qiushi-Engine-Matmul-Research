import FrozenRegistry.Btp287SectionBlock0
import FrozenRegistry.Btp287SectionBlock1
import FrozenRegistry.Btp287SectionBlock2
import FrozenRegistry.Btp287SectionBlock3
import FrozenRegistry.Btp287SectionBlock4
import FrozenRegistry.Btp287SectionBlock5
import FrozenRegistry.Btp287SectionBlock6
import FrozenRegistry.Btp287SectionBlock7
import FrozenRegistry.Btp287SectionBlock8
import FrozenRegistry.Btp287SectionBlock9
import FrozenRegistry.Btp287SectionBlock10
import FrozenRegistry.Btp287SectionBlock11
import FrozenRegistry.Btp287SectionBlock12
import FrozenRegistry.Btp287SectionBlock13
import FrozenRegistry.Btp287SectionBlock14
import FrozenRegistry.Btp287SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane287BtpGenSectionAll : forall i, plane287BtpGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane287BtpGenSectionBlock0
  | ⟨1, _⟩ => exact plane287BtpGenSectionBlock1
  | ⟨2, _⟩ => exact plane287BtpGenSectionBlock2
  | ⟨3, _⟩ => exact plane287BtpGenSectionBlock3
  | ⟨4, _⟩ => exact plane287BtpGenSectionBlock4
  | ⟨5, _⟩ => exact plane287BtpGenSectionBlock5
  | ⟨6, _⟩ => exact plane287BtpGenSectionBlock6
  | ⟨7, _⟩ => exact plane287BtpGenSectionBlock7
  | ⟨8, _⟩ => exact plane287BtpGenSectionBlock8
  | ⟨9, _⟩ => exact plane287BtpGenSectionBlock9
  | ⟨10, _⟩ => exact plane287BtpGenSectionBlock10
  | ⟨11, _⟩ => exact plane287BtpGenSectionBlock11
  | ⟨12, _⟩ => exact plane287BtpGenSectionBlock12
  | ⟨13, _⟩ => exact plane287BtpGenSectionBlock13
  | ⟨14, _⟩ => exact plane287BtpGenSectionBlock14
  | ⟨15, _⟩ => exact plane287BtpGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
