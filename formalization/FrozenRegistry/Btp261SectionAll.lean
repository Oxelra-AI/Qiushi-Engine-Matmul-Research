import FrozenRegistry.Btp261SectionBlock0
import FrozenRegistry.Btp261SectionBlock1
import FrozenRegistry.Btp261SectionBlock2
import FrozenRegistry.Btp261SectionBlock3
import FrozenRegistry.Btp261SectionBlock4
import FrozenRegistry.Btp261SectionBlock5
import FrozenRegistry.Btp261SectionBlock6
import FrozenRegistry.Btp261SectionBlock7
import FrozenRegistry.Btp261SectionBlock8
import FrozenRegistry.Btp261SectionBlock9
import FrozenRegistry.Btp261SectionBlock10
import FrozenRegistry.Btp261SectionBlock11
import FrozenRegistry.Btp261SectionBlock12
import FrozenRegistry.Btp261SectionBlock13
import FrozenRegistry.Btp261SectionBlock14
import FrozenRegistry.Btp261SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane261BtpGenSectionAll : forall i, plane261BtpGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane261BtpGenSectionBlock0
  | ⟨1, _⟩ => exact plane261BtpGenSectionBlock1
  | ⟨2, _⟩ => exact plane261BtpGenSectionBlock2
  | ⟨3, _⟩ => exact plane261BtpGenSectionBlock3
  | ⟨4, _⟩ => exact plane261BtpGenSectionBlock4
  | ⟨5, _⟩ => exact plane261BtpGenSectionBlock5
  | ⟨6, _⟩ => exact plane261BtpGenSectionBlock6
  | ⟨7, _⟩ => exact plane261BtpGenSectionBlock7
  | ⟨8, _⟩ => exact plane261BtpGenSectionBlock8
  | ⟨9, _⟩ => exact plane261BtpGenSectionBlock9
  | ⟨10, _⟩ => exact plane261BtpGenSectionBlock10
  | ⟨11, _⟩ => exact plane261BtpGenSectionBlock11
  | ⟨12, _⟩ => exact plane261BtpGenSectionBlock12
  | ⟨13, _⟩ => exact plane261BtpGenSectionBlock13
  | ⟨14, _⟩ => exact plane261BtpGenSectionBlock14
  | ⟨15, _⟩ => exact plane261BtpGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
