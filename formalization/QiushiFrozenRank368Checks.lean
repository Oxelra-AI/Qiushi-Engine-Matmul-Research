import QiushiFiniteBlocks
import QiushiFrozenRank368Data
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane368RankCoverGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 20, (plane368RankCoverGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane368RankCoverGenConfig.planeBasis (i.val ^^^ (plane368RankCoverGenConfig.sectionCode j).val) = true
abbrev plane368RankCoverGenDeadProperty (i : Fin 512) : Prop :=
  (plane368RankCoverGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane368RankCoverGenConfig.deadBasis (plane368RankCoverGenConfig.deadCover i)) i.val = true
abbrev plane368RankCoverGenSourceProperty (i : Fin 25) : Prop :=
  forall g : Nat, g ∈ plane368RankCoverGenConfig.planeBasis -> spanContainsCode (plane368RankCoverGenConfig.sourceBasis i) g = true
abbrev plane368RankCoverGenDeadSourceProperty (i : Fin 12) : Prop :=
  forall g : Nat, g ∈ plane368RankCoverGenConfig.planeBasis -> spanContainsCode (plane368RankCoverGenConfig.deadBasis i) g = true
abbrev plane368RankCoverGenIndicatorProperty (i : Fin 25) : Prop :=
  forall j : Fin 20, plane368RankCoverGenConfig.occSys.occCoeff i j = if spanContainsCode (plane368RankCoverGenConfig.sourceBasis i) (plane368RankCoverGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenDeadBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 512,
    plane368RankCoverGenDeadProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane368RankCoverGenDeadProperty, plane368RankCoverGenConfig, plane368RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenDeadBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 512,
    plane368RankCoverGenDeadProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane368RankCoverGenDeadProperty, plane368RankCoverGenConfig, plane368RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenDeadBlock2 : forall offset : Fin 32,
    forall hlt : 2 * 32 + offset.val < 512,
    plane368RankCoverGenDeadProperty (Fin.mk (2 * 32 + offset.val) hlt) := by
  simp only [plane368RankCoverGenDeadProperty, plane368RankCoverGenConfig, plane368RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenDeadBlock3 : forall offset : Fin 32,
    forall hlt : 3 * 32 + offset.val < 512,
    plane368RankCoverGenDeadProperty (Fin.mk (3 * 32 + offset.val) hlt) := by
  simp only [plane368RankCoverGenDeadProperty, plane368RankCoverGenConfig, plane368RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenDeadBlock4 : forall offset : Fin 32,
    forall hlt : 4 * 32 + offset.val < 512,
    plane368RankCoverGenDeadProperty (Fin.mk (4 * 32 + offset.val) hlt) := by
  simp only [plane368RankCoverGenDeadProperty, plane368RankCoverGenConfig, plane368RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenDeadBlock5 : forall offset : Fin 32,
    forall hlt : 5 * 32 + offset.val < 512,
    plane368RankCoverGenDeadProperty (Fin.mk (5 * 32 + offset.val) hlt) := by
  simp only [plane368RankCoverGenDeadProperty, plane368RankCoverGenConfig, plane368RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenDeadBlock6 : forall offset : Fin 32,
    forall hlt : 6 * 32 + offset.val < 512,
    plane368RankCoverGenDeadProperty (Fin.mk (6 * 32 + offset.val) hlt) := by
  simp only [plane368RankCoverGenDeadProperty, plane368RankCoverGenConfig, plane368RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenDeadBlock7 : forall offset : Fin 32,
    forall hlt : 7 * 32 + offset.val < 512,
    plane368RankCoverGenDeadProperty (Fin.mk (7 * 32 + offset.val) hlt) := by
  simp only [plane368RankCoverGenDeadProperty, plane368RankCoverGenConfig, plane368RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenDeadBlock8 : forall offset : Fin 32,
    forall hlt : 8 * 32 + offset.val < 512,
    plane368RankCoverGenDeadProperty (Fin.mk (8 * 32 + offset.val) hlt) := by
  simp only [plane368RankCoverGenDeadProperty, plane368RankCoverGenConfig, plane368RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenDeadBlock9 : forall offset : Fin 32,
    forall hlt : 9 * 32 + offset.val < 512,
    plane368RankCoverGenDeadProperty (Fin.mk (9 * 32 + offset.val) hlt) := by
  simp only [plane368RankCoverGenDeadProperty, plane368RankCoverGenConfig, plane368RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenDeadBlock10 : forall offset : Fin 32,
    forall hlt : 10 * 32 + offset.val < 512,
    plane368RankCoverGenDeadProperty (Fin.mk (10 * 32 + offset.val) hlt) := by
  simp only [plane368RankCoverGenDeadProperty, plane368RankCoverGenConfig, plane368RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenDeadBlock11 : forall offset : Fin 32,
    forall hlt : 11 * 32 + offset.val < 512,
    plane368RankCoverGenDeadProperty (Fin.mk (11 * 32 + offset.val) hlt) := by
  simp only [plane368RankCoverGenDeadProperty, plane368RankCoverGenConfig, plane368RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenDeadBlock12 : forall offset : Fin 32,
    forall hlt : 12 * 32 + offset.val < 512,
    plane368RankCoverGenDeadProperty (Fin.mk (12 * 32 + offset.val) hlt) := by
  simp only [plane368RankCoverGenDeadProperty, plane368RankCoverGenConfig, plane368RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenDeadBlock13 : forall offset : Fin 32,
    forall hlt : 13 * 32 + offset.val < 512,
    plane368RankCoverGenDeadProperty (Fin.mk (13 * 32 + offset.val) hlt) := by
  simp only [plane368RankCoverGenDeadProperty, plane368RankCoverGenConfig, plane368RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenDeadBlock14 : forall offset : Fin 32,
    forall hlt : 14 * 32 + offset.val < 512,
    plane368RankCoverGenDeadProperty (Fin.mk (14 * 32 + offset.val) hlt) := by
  simp only [plane368RankCoverGenDeadProperty, plane368RankCoverGenConfig, plane368RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenDeadBlock15 : forall offset : Fin 32,
    forall hlt : 15 * 32 + offset.val < 512,
    plane368RankCoverGenDeadProperty (Fin.mk (15 * 32 + offset.val) hlt) := by
  simp only [plane368RankCoverGenDeadProperty, plane368RankCoverGenConfig, plane368RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenDeadAll : forall i, plane368RankCoverGenDeadProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide +kernel) (by decide +kernel)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane368RankCoverGenDeadBlock0
  | ⟨1, _⟩ => exact plane368RankCoverGenDeadBlock1
  | ⟨2, _⟩ => exact plane368RankCoverGenDeadBlock2
  | ⟨3, _⟩ => exact plane368RankCoverGenDeadBlock3
  | ⟨4, _⟩ => exact plane368RankCoverGenDeadBlock4
  | ⟨5, _⟩ => exact plane368RankCoverGenDeadBlock5
  | ⟨6, _⟩ => exact plane368RankCoverGenDeadBlock6
  | ⟨7, _⟩ => exact plane368RankCoverGenDeadBlock7
  | ⟨8, _⟩ => exact plane368RankCoverGenDeadBlock8
  | ⟨9, _⟩ => exact plane368RankCoverGenDeadBlock9
  | ⟨10, _⟩ => exact plane368RankCoverGenDeadBlock10
  | ⟨11, _⟩ => exact plane368RankCoverGenDeadBlock11
  | ⟨12, _⟩ => exact plane368RankCoverGenDeadBlock12
  | ⟨13, _⟩ => exact plane368RankCoverGenDeadBlock13
  | ⟨14, _⟩ => exact plane368RankCoverGenDeadBlock14
  | ⟨15, _⟩ => exact plane368RankCoverGenDeadBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenDeadSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 12,
    plane368RankCoverGenDeadSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane368RankCoverGenDeadSourceProperty, plane368RankCoverGenConfig, plane368RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenDeadSourceAll : forall i, plane368RankCoverGenDeadSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 1) (width := 32)
    (by decide +kernel) (by decide +kernel)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane368RankCoverGenDeadSourceBlock0
  | ⟨k + 1, h⟩ => omega
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenIndicatorBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 25,
    plane368RankCoverGenIndicatorProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane368RankCoverGenIndicatorProperty, plane368RankCoverGenConfig, plane368RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenIndicatorAll : forall i, plane368RankCoverGenIndicatorProperty i := by
  apply forall_fin_of_blocks (blocks := 1) (width := 32)
    (by decide +kernel) (by decide +kernel)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane368RankCoverGenIndicatorBlock0
  | ⟨k + 1, h⟩ => omega
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenSectionBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 512,
    plane368RankCoverGenSectionProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane368RankCoverGenSectionProperty, plane368RankCoverGenConfig, plane368RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenSectionBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 512,
    plane368RankCoverGenSectionProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane368RankCoverGenSectionProperty, plane368RankCoverGenConfig, plane368RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenSectionBlock2 : forall offset : Fin 32,
    forall hlt : 2 * 32 + offset.val < 512,
    plane368RankCoverGenSectionProperty (Fin.mk (2 * 32 + offset.val) hlt) := by
  simp only [plane368RankCoverGenSectionProperty, plane368RankCoverGenConfig, plane368RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenSectionBlock3 : forall offset : Fin 32,
    forall hlt : 3 * 32 + offset.val < 512,
    plane368RankCoverGenSectionProperty (Fin.mk (3 * 32 + offset.val) hlt) := by
  simp only [plane368RankCoverGenSectionProperty, plane368RankCoverGenConfig, plane368RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenSectionBlock4 : forall offset : Fin 32,
    forall hlt : 4 * 32 + offset.val < 512,
    plane368RankCoverGenSectionProperty (Fin.mk (4 * 32 + offset.val) hlt) := by
  simp only [plane368RankCoverGenSectionProperty, plane368RankCoverGenConfig, plane368RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenSectionBlock5 : forall offset : Fin 32,
    forall hlt : 5 * 32 + offset.val < 512,
    plane368RankCoverGenSectionProperty (Fin.mk (5 * 32 + offset.val) hlt) := by
  simp only [plane368RankCoverGenSectionProperty, plane368RankCoverGenConfig, plane368RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenSectionBlock6 : forall offset : Fin 32,
    forall hlt : 6 * 32 + offset.val < 512,
    plane368RankCoverGenSectionProperty (Fin.mk (6 * 32 + offset.val) hlt) := by
  simp only [plane368RankCoverGenSectionProperty, plane368RankCoverGenConfig, plane368RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenSectionBlock7 : forall offset : Fin 32,
    forall hlt : 7 * 32 + offset.val < 512,
    plane368RankCoverGenSectionProperty (Fin.mk (7 * 32 + offset.val) hlt) := by
  simp only [plane368RankCoverGenSectionProperty, plane368RankCoverGenConfig, plane368RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenSectionBlock8 : forall offset : Fin 32,
    forall hlt : 8 * 32 + offset.val < 512,
    plane368RankCoverGenSectionProperty (Fin.mk (8 * 32 + offset.val) hlt) := by
  simp only [plane368RankCoverGenSectionProperty, plane368RankCoverGenConfig, plane368RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenSectionBlock9 : forall offset : Fin 32,
    forall hlt : 9 * 32 + offset.val < 512,
    plane368RankCoverGenSectionProperty (Fin.mk (9 * 32 + offset.val) hlt) := by
  simp only [plane368RankCoverGenSectionProperty, plane368RankCoverGenConfig, plane368RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenSectionBlock10 : forall offset : Fin 32,
    forall hlt : 10 * 32 + offset.val < 512,
    plane368RankCoverGenSectionProperty (Fin.mk (10 * 32 + offset.val) hlt) := by
  simp only [plane368RankCoverGenSectionProperty, plane368RankCoverGenConfig, plane368RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenSectionBlock11 : forall offset : Fin 32,
    forall hlt : 11 * 32 + offset.val < 512,
    plane368RankCoverGenSectionProperty (Fin.mk (11 * 32 + offset.val) hlt) := by
  simp only [plane368RankCoverGenSectionProperty, plane368RankCoverGenConfig, plane368RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenSectionBlock12 : forall offset : Fin 32,
    forall hlt : 12 * 32 + offset.val < 512,
    plane368RankCoverGenSectionProperty (Fin.mk (12 * 32 + offset.val) hlt) := by
  simp only [plane368RankCoverGenSectionProperty, plane368RankCoverGenConfig, plane368RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenSectionBlock13 : forall offset : Fin 32,
    forall hlt : 13 * 32 + offset.val < 512,
    plane368RankCoverGenSectionProperty (Fin.mk (13 * 32 + offset.val) hlt) := by
  simp only [plane368RankCoverGenSectionProperty, plane368RankCoverGenConfig, plane368RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenSectionBlock14 : forall offset : Fin 32,
    forall hlt : 14 * 32 + offset.val < 512,
    plane368RankCoverGenSectionProperty (Fin.mk (14 * 32 + offset.val) hlt) := by
  simp only [plane368RankCoverGenSectionProperty, plane368RankCoverGenConfig, plane368RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenSectionBlock15 : forall offset : Fin 32,
    forall hlt : 15 * 32 + offset.val < 512,
    plane368RankCoverGenSectionProperty (Fin.mk (15 * 32 + offset.val) hlt) := by
  simp only [plane368RankCoverGenSectionProperty, plane368RankCoverGenConfig, plane368RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenSectionAll : forall i, plane368RankCoverGenSectionProperty i := by
  apply forall_fin_of_blocks (blocks := 16) (width := 32)
    (by decide +kernel) (by decide +kernel)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane368RankCoverGenSectionBlock0
  | ⟨1, _⟩ => exact plane368RankCoverGenSectionBlock1
  | ⟨2, _⟩ => exact plane368RankCoverGenSectionBlock2
  | ⟨3, _⟩ => exact plane368RankCoverGenSectionBlock3
  | ⟨4, _⟩ => exact plane368RankCoverGenSectionBlock4
  | ⟨5, _⟩ => exact plane368RankCoverGenSectionBlock5
  | ⟨6, _⟩ => exact plane368RankCoverGenSectionBlock6
  | ⟨7, _⟩ => exact plane368RankCoverGenSectionBlock7
  | ⟨8, _⟩ => exact plane368RankCoverGenSectionBlock8
  | ⟨9, _⟩ => exact plane368RankCoverGenSectionBlock9
  | ⟨10, _⟩ => exact plane368RankCoverGenSectionBlock10
  | ⟨11, _⟩ => exact plane368RankCoverGenSectionBlock11
  | ⟨12, _⟩ => exact plane368RankCoverGenSectionBlock12
  | ⟨13, _⟩ => exact plane368RankCoverGenSectionBlock13
  | ⟨14, _⟩ => exact plane368RankCoverGenSectionBlock14
  | ⟨15, _⟩ => exact plane368RankCoverGenSectionBlock15
  | ⟨k + 16, h⟩ => omega
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 25,
    plane368RankCoverGenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane368RankCoverGenSourceProperty, plane368RankCoverGenConfig, plane368RankCoverGenOccSys]
  decide +kernel
end QiushiMatmul

set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenSourceAll : forall i, plane368RankCoverGenSourceProperty i := by
  apply forall_fin_of_blocks (blocks := 1) (width := 32)
    (by decide +kernel) (by decide +kernel)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane368RankCoverGenSourceBlock0
  | ⟨k + 1, h⟩ => omega
end QiushiMatmul
