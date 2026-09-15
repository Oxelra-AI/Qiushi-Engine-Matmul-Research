import FrozenRegistry.Btp285SectionBlock0
import FrozenRegistry.Btp285SectionBlock1
import FrozenRegistry.Btp285SectionBlock2
import FrozenRegistry.Btp285SectionBlock3
import FrozenRegistry.Btp285SectionBlock4
import FrozenRegistry.Btp285SectionBlock5
import FrozenRegistry.Btp285SectionBlock6
import FrozenRegistry.Btp285SectionBlock7
import FrozenRegistry.Btp285SectionBlock8
import FrozenRegistry.Btp285SectionBlock9
import FrozenRegistry.Btp285SectionBlock10
import FrozenRegistry.Btp285SectionBlock11
import FrozenRegistry.Btp285SectionBlock12
import FrozenRegistry.Btp285SectionBlock13
import FrozenRegistry.Btp285SectionBlock14
import FrozenRegistry.Btp285SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane285BtpGenSectionAll : forall i, plane285BtpGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane285BtpGenSectionBlock0
  | ⟨1, _⟩ => exact plane285BtpGenSectionBlock1
  | ⟨2, _⟩ => exact plane285BtpGenSectionBlock2
  | ⟨3, _⟩ => exact plane285BtpGenSectionBlock3
  | ⟨4, _⟩ => exact plane285BtpGenSectionBlock4
  | ⟨5, _⟩ => exact plane285BtpGenSectionBlock5
  | ⟨6, _⟩ => exact plane285BtpGenSectionBlock6
  | ⟨7, _⟩ => exact plane285BtpGenSectionBlock7
  | ⟨8, _⟩ => exact plane285BtpGenSectionBlock8
  | ⟨9, _⟩ => exact plane285BtpGenSectionBlock9
  | ⟨10, _⟩ => exact plane285BtpGenSectionBlock10
  | ⟨11, _⟩ => exact plane285BtpGenSectionBlock11
  | ⟨12, _⟩ => exact plane285BtpGenSectionBlock12
  | ⟨13, _⟩ => exact plane285BtpGenSectionBlock13
  | ⟨14, _⟩ => exact plane285BtpGenSectionBlock14
  | ⟨15, _⟩ => exact plane285BtpGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
