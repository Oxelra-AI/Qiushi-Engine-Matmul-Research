import QiushiFiniteBlocks
import QiushiFrozenRank367Data
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane367RankCoverGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 24, (plane367RankCoverGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane367RankCoverGenConfig.planeBasis (i.val ^^^ (plane367RankCoverGenConfig.sectionCode j).val) = true
abbrev plane367RankCoverGenDeadProperty (i : Fin 512) : Prop :=
  (plane367RankCoverGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane367RankCoverGenConfig.deadBasis (plane367RankCoverGenConfig.deadCover i)) i.val = true
abbrev plane367RankCoverGenSourceProperty (i : Fin 70) : Prop :=
  forall g : Nat, g ∈ plane367RankCoverGenConfig.planeBasis -> spanContainsCode (plane367RankCoverGenConfig.sourceBasis i) g = true
abbrev plane367RankCoverGenDeadSourceProperty (i : Fin 7) : Prop :=
  forall g : Nat, g ∈ plane367RankCoverGenConfig.planeBasis -> spanContainsCode (plane367RankCoverGenConfig.deadBasis i) g = true
abbrev plane367RankCoverGenIndicatorProperty (i : Fin 70) : Prop :=
  forall j : Fin 24, plane367RankCoverGenConfig.occSys.occCoeff i j = if spanContainsCode (plane367RankCoverGenConfig.sourceBasis i) (plane367RankCoverGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenDeadBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 512,
    plane367RankCoverGenDeadProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenDeadProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenDeadBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 512,
    plane367RankCoverGenDeadProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenDeadProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenDeadBlock2 : forall offset : Fin 32,
    forall hlt : 2 * 32 + offset.val < 512,
    plane367RankCoverGenDeadProperty (Fin.mk (2 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenDeadProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenDeadBlock3 : forall offset : Fin 32,
    forall hlt : 3 * 32 + offset.val < 512,
    plane367RankCoverGenDeadProperty (Fin.mk (3 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenDeadProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenDeadBlock4 : forall offset : Fin 32,
    forall hlt : 4 * 32 + offset.val < 512,
    plane367RankCoverGenDeadProperty (Fin.mk (4 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenDeadProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenDeadBlock5 : forall offset : Fin 32,
    forall hlt : 5 * 32 + offset.val < 512,
    plane367RankCoverGenDeadProperty (Fin.mk (5 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenDeadProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenDeadBlock6 : forall offset : Fin 32,
    forall hlt : 6 * 32 + offset.val < 512,
    plane367RankCoverGenDeadProperty (Fin.mk (6 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenDeadProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenDeadBlock7 : forall offset : Fin 32,
    forall hlt : 7 * 32 + offset.val < 512,
    plane367RankCoverGenDeadProperty (Fin.mk (7 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenDeadProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenDeadBlock8 : forall offset : Fin 32,
    forall hlt : 8 * 32 + offset.val < 512,
    plane367RankCoverGenDeadProperty (Fin.mk (8 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenDeadProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenDeadBlock9 : forall offset : Fin 32,
    forall hlt : 9 * 32 + offset.val < 512,
    plane367RankCoverGenDeadProperty (Fin.mk (9 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenDeadProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenDeadBlock10 : forall offset : Fin 32,
    forall hlt : 10 * 32 + offset.val < 512,
    plane367RankCoverGenDeadProperty (Fin.mk (10 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenDeadProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenDeadBlock11 : forall offset : Fin 32,
    forall hlt : 11 * 32 + offset.val < 512,
    plane367RankCoverGenDeadProperty (Fin.mk (11 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenDeadProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenDeadBlock12 : forall offset : Fin 32,
    forall hlt : 12 * 32 + offset.val < 512,
    plane367RankCoverGenDeadProperty (Fin.mk (12 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenDeadProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenDeadBlock13 : forall offset : Fin 32,
    forall hlt : 13 * 32 + offset.val < 512,
    plane367RankCoverGenDeadProperty (Fin.mk (13 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenDeadProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenDeadBlock14 : forall offset : Fin 32,
    forall hlt : 14 * 32 + offset.val < 512,
    plane367RankCoverGenDeadProperty (Fin.mk (14 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenDeadProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenDeadBlock15 : forall offset : Fin 32,
    forall hlt : 15 * 32 + offset.val < 512,
    plane367RankCoverGenDeadProperty (Fin.mk (15 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenDeadProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenDeadAll : forall i, plane367RankCoverGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide +kernel) (by decide +kernel)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane367RankCoverGenDeadBlock0
  | ⟨1, _⟩ => exact plane367RankCoverGenDeadBlock1
  | ⟨2, _⟩ => exact plane367RankCoverGenDeadBlock2
  | ⟨3, _⟩ => exact plane367RankCoverGenDeadBlock3
  | ⟨4, _⟩ => exact plane367RankCoverGenDeadBlock4
  | ⟨5, _⟩ => exact plane367RankCoverGenDeadBlock5
  | ⟨6, _⟩ => exact plane367RankCoverGenDeadBlock6
  | ⟨7, _⟩ => exact plane367RankCoverGenDeadBlock7
  | ⟨8, _⟩ => exact plane367RankCoverGenDeadBlock8
  | ⟨9, _⟩ => exact plane367RankCoverGenDeadBlock9
  | ⟨10, _⟩ => exact plane367RankCoverGenDeadBlock10
  | ⟨11, _⟩ => exact plane367RankCoverGenDeadBlock11
  | ⟨12, _⟩ => exact plane367RankCoverGenDeadBlock12
  | ⟨13, _⟩ => exact plane367RankCoverGenDeadBlock13
  | ⟨14, _⟩ => exact plane367RankCoverGenDeadBlock14
  | ⟨15, _⟩ => exact plane367RankCoverGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenDeadSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 7,
    plane367RankCoverGenDeadSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenDeadSourceProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenDeadSourceAll : forall i, plane367RankCoverGenDeadSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 1) (width := 32)
    (by decide +kernel) (by decide +kernel)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane367RankCoverGenDeadSourceBlock0
  | ⟨k + 1, h⟩ => omega
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenIndicatorBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 70,
    plane367RankCoverGenIndicatorProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenIndicatorProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenIndicatorBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 70,
    plane367RankCoverGenIndicatorProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenIndicatorProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenIndicatorBlock2 : forall offset : Fin 32,
    forall hlt : 2 * 32 + offset.val < 70,
    plane367RankCoverGenIndicatorProperty (Fin.mk (2 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenIndicatorProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenIndicatorAll : forall i, plane367RankCoverGenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 3) (width := 32)
    (by decide +kernel) (by decide +kernel)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane367RankCoverGenIndicatorBlock0
  | ⟨1, _⟩ => exact plane367RankCoverGenIndicatorBlock1
  | ⟨2, _⟩ => exact plane367RankCoverGenIndicatorBlock2
  | ⟨k + 3, h⟩ => omega
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenSectionBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 512,
    plane367RankCoverGenSectionProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenSectionProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenSectionBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 512,
    plane367RankCoverGenSectionProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenSectionProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenSectionBlock2 : forall offset : Fin 32,
    forall hlt : 2 * 32 + offset.val < 512,
    plane367RankCoverGenSectionProperty (Fin.mk (2 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenSectionProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenSectionBlock3 : forall offset : Fin 32,
    forall hlt : 3 * 32 + offset.val < 512,
    plane367RankCoverGenSectionProperty (Fin.mk (3 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenSectionProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenSectionBlock4 : forall offset : Fin 32,
    forall hlt : 4 * 32 + offset.val < 512,
    plane367RankCoverGenSectionProperty (Fin.mk (4 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenSectionProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenSectionBlock5 : forall offset : Fin 32,
    forall hlt : 5 * 32 + offset.val < 512,
    plane367RankCoverGenSectionProperty (Fin.mk (5 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenSectionProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenSectionBlock6 : forall offset : Fin 32,
    forall hlt : 6 * 32 + offset.val < 512,
    plane367RankCoverGenSectionProperty (Fin.mk (6 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenSectionProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenSectionBlock7 : forall offset : Fin 32,
    forall hlt : 7 * 32 + offset.val < 512,
    plane367RankCoverGenSectionProperty (Fin.mk (7 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenSectionProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenSectionBlock8 : forall offset : Fin 32,
    forall hlt : 8 * 32 + offset.val < 512,
    plane367RankCoverGenSectionProperty (Fin.mk (8 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenSectionProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenSectionBlock9 : forall offset : Fin 32,
    forall hlt : 9 * 32 + offset.val < 512,
    plane367RankCoverGenSectionProperty (Fin.mk (9 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenSectionProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenSectionBlock10 : forall offset : Fin 32,
    forall hlt : 10 * 32 + offset.val < 512,
    plane367RankCoverGenSectionProperty (Fin.mk (10 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenSectionProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenSectionBlock11 : forall offset : Fin 32,
    forall hlt : 11 * 32 + offset.val < 512,
    plane367RankCoverGenSectionProperty (Fin.mk (11 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenSectionProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenSectionBlock12 : forall offset : Fin 32,
    forall hlt : 12 * 32 + offset.val < 512,
    plane367RankCoverGenSectionProperty (Fin.mk (12 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenSectionProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenSectionBlock13 : forall offset : Fin 32,
    forall hlt : 13 * 32 + offset.val < 512,
    plane367RankCoverGenSectionProperty (Fin.mk (13 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenSectionProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenSectionBlock14 : forall offset : Fin 32,
    forall hlt : 14 * 32 + offset.val < 512,
    plane367RankCoverGenSectionProperty (Fin.mk (14 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenSectionProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenSectionBlock15 : forall offset : Fin 32,
    forall hlt : 15 * 32 + offset.val < 512,
    plane367RankCoverGenSectionProperty (Fin.mk (15 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenSectionProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenSectionAll : forall i, plane367RankCoverGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide +kernel) (by decide +kernel)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane367RankCoverGenSectionBlock0
  | ⟨1, _⟩ => exact plane367RankCoverGenSectionBlock1
  | ⟨2, _⟩ => exact plane367RankCoverGenSectionBlock2
  | ⟨3, _⟩ => exact plane367RankCoverGenSectionBlock3
  | ⟨4, _⟩ => exact plane367RankCoverGenSectionBlock4
  | ⟨5, _⟩ => exact plane367RankCoverGenSectionBlock5
  | ⟨6, _⟩ => exact plane367RankCoverGenSectionBlock6
  | ⟨7, _⟩ => exact plane367RankCoverGenSectionBlock7
  | ⟨8, _⟩ => exact plane367RankCoverGenSectionBlock8
  | ⟨9, _⟩ => exact plane367RankCoverGenSectionBlock9
  | ⟨10, _⟩ => exact plane367RankCoverGenSectionBlock10
  | ⟨11, _⟩ => exact plane367RankCoverGenSectionBlock11
  | ⟨12, _⟩ => exact plane367RankCoverGenSectionBlock12
  | ⟨13, _⟩ => exact plane367RankCoverGenSectionBlock13
  | ⟨14, _⟩ => exact plane367RankCoverGenSectionBlock14
  | ⟨15, _⟩ => exact plane367RankCoverGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 70,
    plane367RankCoverGenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenSourceProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenSourceBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 70,
    plane367RankCoverGenSourceProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenSourceProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenSourceBlock2 : forall offset : Fin 32,
    forall hlt : 2 * 32 + offset.val < 70,
    plane367RankCoverGenSourceProperty (Fin.mk (2 * 32 + offset.val) hlt) := by
  simp only [plane367RankCoverGenSourceProperty, plane367RankCoverGenConfig, plane367RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenSourceAll : forall i, plane367RankCoverGenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 3) (width := 32)
    (by decide +kernel) (by decide +kernel)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane367RankCoverGenSourceBlock0
  | ⟨1, _⟩ => exact plane367RankCoverGenSourceBlock1
  | ⟨2, _⟩ => exact plane367RankCoverGenSourceBlock2
  | ⟨k + 3, h⟩ => omega
end QiushiMatmul
