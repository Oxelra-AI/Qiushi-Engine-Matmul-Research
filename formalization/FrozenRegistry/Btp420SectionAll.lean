import FrozenRegistry.Btp420SectionBlock0
import FrozenRegistry.Btp420SectionBlock1
import FrozenRegistry.Btp420SectionBlock2
import FrozenRegistry.Btp420SectionBlock3
import FrozenRegistry.Btp420SectionBlock4
import FrozenRegistry.Btp420SectionBlock5
import FrozenRegistry.Btp420SectionBlock6
import FrozenRegistry.Btp420SectionBlock7
import FrozenRegistry.Btp420SectionBlock8
import FrozenRegistry.Btp420SectionBlock9
import FrozenRegistry.Btp420SectionBlock10
import FrozenRegistry.Btp420SectionBlock11
import FrozenRegistry.Btp420SectionBlock12
import FrozenRegistry.Btp420SectionBlock13
import FrozenRegistry.Btp420SectionBlock14
import FrozenRegistry.Btp420SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane420BtpGenSectionAll : forall i, plane420BtpGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane420BtpGenSectionBlock0
  | ⟨1, _⟩ => exact plane420BtpGenSectionBlock1
  | ⟨2, _⟩ => exact plane420BtpGenSectionBlock2
  | ⟨3, _⟩ => exact plane420BtpGenSectionBlock3
  | ⟨4, _⟩ => exact plane420BtpGenSectionBlock4
  | ⟨5, _⟩ => exact plane420BtpGenSectionBlock5
  | ⟨6, _⟩ => exact plane420BtpGenSectionBlock6
  | ⟨7, _⟩ => exact plane420BtpGenSectionBlock7
  | ⟨8, _⟩ => exact plane420BtpGenSectionBlock8
  | ⟨9, _⟩ => exact plane420BtpGenSectionBlock9
  | ⟨10, _⟩ => exact plane420BtpGenSectionBlock10
  | ⟨11, _⟩ => exact plane420BtpGenSectionBlock11
  | ⟨12, _⟩ => exact plane420BtpGenSectionBlock12
  | ⟨13, _⟩ => exact plane420BtpGenSectionBlock13
  | ⟨14, _⟩ => exact plane420BtpGenSectionBlock14
  | ⟨15, _⟩ => exact plane420BtpGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
