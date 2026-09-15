import FrozenRegistry.Btp224SectionBlock0
import FrozenRegistry.Btp224SectionBlock1
import FrozenRegistry.Btp224SectionBlock2
import FrozenRegistry.Btp224SectionBlock3
import FrozenRegistry.Btp224SectionBlock4
import FrozenRegistry.Btp224SectionBlock5
import FrozenRegistry.Btp224SectionBlock6
import FrozenRegistry.Btp224SectionBlock7
import FrozenRegistry.Btp224SectionBlock8
import FrozenRegistry.Btp224SectionBlock9
import FrozenRegistry.Btp224SectionBlock10
import FrozenRegistry.Btp224SectionBlock11
import FrozenRegistry.Btp224SectionBlock12
import FrozenRegistry.Btp224SectionBlock13
import FrozenRegistry.Btp224SectionBlock14
import FrozenRegistry.Btp224SectionBlock15
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane224BtpGenSectionAll : forall i, plane224BtpGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane224BtpGenSectionBlock0
  | ⟨1, _⟩ => exact plane224BtpGenSectionBlock1
  | ⟨2, _⟩ => exact plane224BtpGenSectionBlock2
  | ⟨3, _⟩ => exact plane224BtpGenSectionBlock3
  | ⟨4, _⟩ => exact plane224BtpGenSectionBlock4
  | ⟨5, _⟩ => exact plane224BtpGenSectionBlock5
  | ⟨6, _⟩ => exact plane224BtpGenSectionBlock6
  | ⟨7, _⟩ => exact plane224BtpGenSectionBlock7
  | ⟨8, _⟩ => exact plane224BtpGenSectionBlock8
  | ⟨9, _⟩ => exact plane224BtpGenSectionBlock9
  | ⟨10, _⟩ => exact plane224BtpGenSectionBlock10
  | ⟨11, _⟩ => exact plane224BtpGenSectionBlock11
  | ⟨12, _⟩ => exact plane224BtpGenSectionBlock12
  | ⟨13, _⟩ => exact plane224BtpGenSectionBlock13
  | ⟨14, _⟩ => exact plane224BtpGenSectionBlock14
  | ⟨15, _⟩ => exact plane224BtpGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul
