import QiushiFiniteBlocks
import QiushiFrozenRank361Data
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane361RankCoverGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 24, (plane361RankCoverGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane361RankCoverGenConfig.planeBasis (i.val ^^^ (plane361RankCoverGenConfig.sectionCode j).val) = true
abbrev plane361RankCoverGenDeadProperty (i : Fin 512) : Prop :=
  (plane361RankCoverGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane361RankCoverGenConfig.deadBasis (plane361RankCoverGenConfig.deadCover i)) i.val = true
abbrev plane361RankCoverGenSourceProperty (i : Fin 86) : Prop :=
  forall g : Nat, g ∈ plane361RankCoverGenConfig.planeBasis -> spanContainsCode (plane361RankCoverGenConfig.sourceBasis i) g = true
abbrev plane361RankCoverGenDeadSourceProperty (i : Fin 7) : Prop :=
  forall g : Nat, g ∈ plane361RankCoverGenConfig.planeBasis -> spanContainsCode (plane361RankCoverGenConfig.deadBasis i) g = true
abbrev plane361RankCoverGenIndicatorProperty (i : Fin 86) : Prop :=
  forall j : Fin 24, plane361RankCoverGenConfig.occSys.occCoeff i j = if spanContainsCode (plane361RankCoverGenConfig.sourceBasis i) (plane361RankCoverGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenDeadBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 512,
    plane361RankCoverGenDeadProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenDeadProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenDeadBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 512,
    plane361RankCoverGenDeadProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenDeadProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenDeadBlock2 : forall offset : Fin 32,
    forall hlt : 2 * 32 + offset.val < 512,
    plane361RankCoverGenDeadProperty (Fin.mk (2 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenDeadProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenDeadBlock3 : forall offset : Fin 32,
    forall hlt : 3 * 32 + offset.val < 512,
    plane361RankCoverGenDeadProperty (Fin.mk (3 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenDeadProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenDeadBlock4 : forall offset : Fin 32,
    forall hlt : 4 * 32 + offset.val < 512,
    plane361RankCoverGenDeadProperty (Fin.mk (4 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenDeadProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenDeadBlock5 : forall offset : Fin 32,
    forall hlt : 5 * 32 + offset.val < 512,
    plane361RankCoverGenDeadProperty (Fin.mk (5 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenDeadProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenDeadBlock6 : forall offset : Fin 32,
    forall hlt : 6 * 32 + offset.val < 512,
    plane361RankCoverGenDeadProperty (Fin.mk (6 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenDeadProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenDeadBlock7 : forall offset : Fin 32,
    forall hlt : 7 * 32 + offset.val < 512,
    plane361RankCoverGenDeadProperty (Fin.mk (7 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenDeadProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenDeadBlock8 : forall offset : Fin 32,
    forall hlt : 8 * 32 + offset.val < 512,
    plane361RankCoverGenDeadProperty (Fin.mk (8 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenDeadProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenDeadBlock9 : forall offset : Fin 32,
    forall hlt : 9 * 32 + offset.val < 512,
    plane361RankCoverGenDeadProperty (Fin.mk (9 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenDeadProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenDeadBlock10 : forall offset : Fin 32,
    forall hlt : 10 * 32 + offset.val < 512,
    plane361RankCoverGenDeadProperty (Fin.mk (10 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenDeadProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenDeadBlock11 : forall offset : Fin 32,
    forall hlt : 11 * 32 + offset.val < 512,
    plane361RankCoverGenDeadProperty (Fin.mk (11 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenDeadProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenDeadBlock12 : forall offset : Fin 32,
    forall hlt : 12 * 32 + offset.val < 512,
    plane361RankCoverGenDeadProperty (Fin.mk (12 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenDeadProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenDeadBlock13 : forall offset : Fin 32,
    forall hlt : 13 * 32 + offset.val < 512,
    plane361RankCoverGenDeadProperty (Fin.mk (13 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenDeadProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenDeadBlock14 : forall offset : Fin 32,
    forall hlt : 14 * 32 + offset.val < 512,
    plane361RankCoverGenDeadProperty (Fin.mk (14 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenDeadProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenDeadBlock15 : forall offset : Fin 32,
    forall hlt : 15 * 32 + offset.val < 512,
    plane361RankCoverGenDeadProperty (Fin.mk (15 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenDeadProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenDeadAll : forall i, plane361RankCoverGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide +kernel) (by decide +kernel)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane361RankCoverGenDeadBlock0
  | ⟨1, _⟩ => exact plane361RankCoverGenDeadBlock1
  | ⟨2, _⟩ => exact plane361RankCoverGenDeadBlock2
  | ⟨3, _⟩ => exact plane361RankCoverGenDeadBlock3
  | ⟨4, _⟩ => exact plane361RankCoverGenDeadBlock4
  | ⟨5, _⟩ => exact plane361RankCoverGenDeadBlock5
  | ⟨6, _⟩ => exact plane361RankCoverGenDeadBlock6
  | ⟨7, _⟩ => exact plane361RankCoverGenDeadBlock7
  | ⟨8, _⟩ => exact plane361RankCoverGenDeadBlock8
  | ⟨9, _⟩ => exact plane361RankCoverGenDeadBlock9
  | ⟨10, _⟩ => exact plane361RankCoverGenDeadBlock10
  | ⟨11, _⟩ => exact plane361RankCoverGenDeadBlock11
  | ⟨12, _⟩ => exact plane361RankCoverGenDeadBlock12
  | ⟨13, _⟩ => exact plane361RankCoverGenDeadBlock13
  | ⟨14, _⟩ => exact plane361RankCoverGenDeadBlock14
  | ⟨15, _⟩ => exact plane361RankCoverGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenDeadSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 7,
    plane361RankCoverGenDeadSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenDeadSourceProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenDeadSourceAll : forall i, plane361RankCoverGenDeadSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 1) (width := 32)
    (by decide +kernel) (by decide +kernel)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane361RankCoverGenDeadSourceBlock0
  | ⟨k + 1, h⟩ => omega
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenIndicatorBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 86,
    plane361RankCoverGenIndicatorProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenIndicatorProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenIndicatorBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 86,
    plane361RankCoverGenIndicatorProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenIndicatorProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenIndicatorBlock2 : forall offset : Fin 32,
    forall hlt : 2 * 32 + offset.val < 86,
    plane361RankCoverGenIndicatorProperty (Fin.mk (2 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenIndicatorProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenIndicatorAll : forall i, plane361RankCoverGenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 3) (width := 32)
    (by decide +kernel) (by decide +kernel)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane361RankCoverGenIndicatorBlock0
  | ⟨1, _⟩ => exact plane361RankCoverGenIndicatorBlock1
  | ⟨2, _⟩ => exact plane361RankCoverGenIndicatorBlock2
  | ⟨k + 3, h⟩ => omega
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenSectionBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 512,
    plane361RankCoverGenSectionProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenSectionProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenSectionBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 512,
    plane361RankCoverGenSectionProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenSectionProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenSectionBlock2 : forall offset : Fin 32,
    forall hlt : 2 * 32 + offset.val < 512,
    plane361RankCoverGenSectionProperty (Fin.mk (2 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenSectionProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenSectionBlock3 : forall offset : Fin 32,
    forall hlt : 3 * 32 + offset.val < 512,
    plane361RankCoverGenSectionProperty (Fin.mk (3 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenSectionProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenSectionBlock4 : forall offset : Fin 32,
    forall hlt : 4 * 32 + offset.val < 512,
    plane361RankCoverGenSectionProperty (Fin.mk (4 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenSectionProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenSectionBlock5 : forall offset : Fin 32,
    forall hlt : 5 * 32 + offset.val < 512,
    plane361RankCoverGenSectionProperty (Fin.mk (5 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenSectionProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenSectionBlock6 : forall offset : Fin 32,
    forall hlt : 6 * 32 + offset.val < 512,
    plane361RankCoverGenSectionProperty (Fin.mk (6 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenSectionProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenSectionBlock7 : forall offset : Fin 32,
    forall hlt : 7 * 32 + offset.val < 512,
    plane361RankCoverGenSectionProperty (Fin.mk (7 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenSectionProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenSectionBlock8 : forall offset : Fin 32,
    forall hlt : 8 * 32 + offset.val < 512,
    plane361RankCoverGenSectionProperty (Fin.mk (8 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenSectionProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenSectionBlock9 : forall offset : Fin 32,
    forall hlt : 9 * 32 + offset.val < 512,
    plane361RankCoverGenSectionProperty (Fin.mk (9 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenSectionProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenSectionBlock10 : forall offset : Fin 32,
    forall hlt : 10 * 32 + offset.val < 512,
    plane361RankCoverGenSectionProperty (Fin.mk (10 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenSectionProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenSectionBlock11 : forall offset : Fin 32,
    forall hlt : 11 * 32 + offset.val < 512,
    plane361RankCoverGenSectionProperty (Fin.mk (11 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenSectionProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenSectionBlock12 : forall offset : Fin 32,
    forall hlt : 12 * 32 + offset.val < 512,
    plane361RankCoverGenSectionProperty (Fin.mk (12 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenSectionProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenSectionBlock13 : forall offset : Fin 32,
    forall hlt : 13 * 32 + offset.val < 512,
    plane361RankCoverGenSectionProperty (Fin.mk (13 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenSectionProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenSectionBlock14 : forall offset : Fin 32,
    forall hlt : 14 * 32 + offset.val < 512,
    plane361RankCoverGenSectionProperty (Fin.mk (14 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenSectionProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenSectionBlock15 : forall offset : Fin 32,
    forall hlt : 15 * 32 + offset.val < 512,
    plane361RankCoverGenSectionProperty (Fin.mk (15 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenSectionProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenSectionAll : forall i, plane361RankCoverGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide +kernel) (by decide +kernel)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane361RankCoverGenSectionBlock0
  | ⟨1, _⟩ => exact plane361RankCoverGenSectionBlock1
  | ⟨2, _⟩ => exact plane361RankCoverGenSectionBlock2
  | ⟨3, _⟩ => exact plane361RankCoverGenSectionBlock3
  | ⟨4, _⟩ => exact plane361RankCoverGenSectionBlock4
  | ⟨5, _⟩ => exact plane361RankCoverGenSectionBlock5
  | ⟨6, _⟩ => exact plane361RankCoverGenSectionBlock6
  | ⟨7, _⟩ => exact plane361RankCoverGenSectionBlock7
  | ⟨8, _⟩ => exact plane361RankCoverGenSectionBlock8
  | ⟨9, _⟩ => exact plane361RankCoverGenSectionBlock9
  | ⟨10, _⟩ => exact plane361RankCoverGenSectionBlock10
  | ⟨11, _⟩ => exact plane361RankCoverGenSectionBlock11
  | ⟨12, _⟩ => exact plane361RankCoverGenSectionBlock12
  | ⟨13, _⟩ => exact plane361RankCoverGenSectionBlock13
  | ⟨14, _⟩ => exact plane361RankCoverGenSectionBlock14
  | ⟨15, _⟩ => exact plane361RankCoverGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 86,
    plane361RankCoverGenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenSourceProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenSourceBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 86,
    plane361RankCoverGenSourceProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenSourceProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenSourceBlock2 : forall offset : Fin 32,
    forall hlt : 2 * 32 + offset.val < 86,
    plane361RankCoverGenSourceProperty (Fin.mk (2 * 32 + offset.val) hlt) := by
  simp only [plane361RankCoverGenSourceProperty, plane361RankCoverGenConfig, plane361RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenSourceAll : forall i, plane361RankCoverGenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 3) (width := 32)
    (by decide +kernel) (by decide +kernel)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane361RankCoverGenSourceBlock0
  | ⟨1, _⟩ => exact plane361RankCoverGenSourceBlock1
  | ⟨2, _⟩ => exact plane361RankCoverGenSourceBlock2
  | ⟨k + 3, h⟩ => omega
end QiushiMatmul
