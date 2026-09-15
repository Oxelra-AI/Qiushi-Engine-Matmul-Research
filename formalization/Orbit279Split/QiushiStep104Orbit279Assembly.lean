import Orbit279Split.QiushiStep104Orbit279Row00
import Orbit279Split.QiushiStep104Orbit279Row01
import Orbit279Split.QiushiStep104Orbit279Row02
import Orbit279Split.QiushiStep104Orbit279Row03
import Orbit279Split.QiushiStep104Orbit279Row04
import Orbit279Split.QiushiStep104Orbit279Row05
import Orbit279Split.QiushiStep104Orbit279Row06
import Orbit279Split.QiushiStep104Orbit279Row07
import Orbit279Split.QiushiStep104Orbit279Row08
import Orbit279Split.QiushiStep104Orbit279Row09
import Orbit279Split.QiushiStep104Orbit279Row10
import Orbit279Split.QiushiStep104Orbit279Row11
import Orbit279Split.QiushiStep104Orbit279Row12
import Orbit279Split.QiushiStep104Orbit279Row13
import Orbit279Split.QiushiStep104Orbit279Row14
import Orbit279Split.QiushiStep104Orbit279Row15
import Orbit279Split.QiushiStep104Orbit279Row16
import Orbit279Split.QiushiStep104Orbit279Row17
import Orbit279Split.QiushiStep104Orbit279Row18
import Orbit279Split.QiushiStep104Orbit279Row19
import Orbit279Split.QiushiStep104Orbit279Row20
import Orbit279Split.QiushiStep104Orbit279Row21
import Orbit279Split.QiushiStep104Orbit279Row22
import Orbit279Split.QiushiStep104Orbit279Row23
import Orbit279Split.QiushiStep104Orbit279Row24
import Orbit279Split.QiushiStep104Orbit279Row25
import Orbit279Split.QiushiStep104Orbit279Row26
import Orbit279Split.QiushiStep104Orbit279Row27
import Orbit279Split.QiushiStep104Orbit279Row28
import Orbit279Split.QiushiStep104Orbit279Row29
import Orbit279Split.QiushiStep104Orbit279Row30
import Orbit279Split.QiushiStep104Orbit279Row31
import Orbit279Split.QiushiStep104Orbit279Row32
import Orbit279Split.QiushiStep104Orbit279Row33
import Orbit279Split.QiushiStep104Orbit279Row34
import Orbit279Split.QiushiStep104Orbit279Row35
import Orbit279Split.QiushiStep104Orbit279Row36
import Orbit279Split.QiushiStep104Orbit279Row37
import Orbit279Split.QiushiStep104Orbit279Row38
import Orbit279Split.QiushiStep104Orbit279Row39
import Orbit279Split.QiushiStep104Orbit279Row40
import Orbit279Split.QiushiStep104Orbit279Row41
import Orbit279Split.QiushiStep104Orbit279Row42
import Orbit279Split.QiushiStep104Orbit279Row43
import Orbit279Split.QiushiStep104Orbit279Row44
import Orbit279Split.QiushiStep104Orbit279Row45
import Orbit279Split.QiushiStep104Orbit279Row46
import Orbit279Split.QiushiStep104Orbit279Row47
import Orbit279Split.QiushiStep104Orbit279Row48
import Orbit279Split.QiushiStep104Orbit279Row49
import Orbit279Split.QiushiStep104Orbit279Row50
import Orbit279Split.QiushiStep104Orbit279Row51
import Orbit279Split.QiushiStep104Orbit279Row52
import Orbit279Split.QiushiStep104Orbit279Row53
import Orbit279Split.QiushiStep104Orbit279Row54
import Orbit279Split.QiushiStep104Orbit279Row55
import Orbit279Split.QiushiStep104Orbit279Row56
import Orbit279Split.QiushiStep104Orbit279Row57
import Orbit279Split.QiushiStep104Orbit279Row58
import Orbit279Split.QiushiStep104Orbit279Row59
import Orbit279Split.QiushiStep104Orbit279Row60
import Orbit279Split.QiushiStep104Orbit279Row61
import Orbit279Split.QiushiStep104Orbit279Row62
import Orbit279Split.QiushiStep104Orbit279Row63

set_option maxHeartbeats 80000000
set_option synthInstance.maxHeartbeats 80000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

theorem o279_extractRootHolds_split (D : QuotientTensorDecomp o279W 16) :
    S_279.RootHolds (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _)) where
  hOcc := by
    intro i
    fin_cases i
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨0, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨0, by decide⟩)
        (coeffMatch279_0)]
      exact rowBound279_0 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨1, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨1, by decide⟩)
        (coeffMatch279_1)]
      exact rowBound279_1 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨2, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨2, by decide⟩)
        (coeffMatch279_2)]
      exact rowBound279_2 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨3, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨3, by decide⟩)
        (coeffMatch279_3)]
      exact rowBound279_3 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨4, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨4, by decide⟩)
        (coeffMatch279_4)]
      exact rowBound279_4 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨5, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨5, by decide⟩)
        (coeffMatch279_5)]
      exact rowBound279_5 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨6, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨6, by decide⟩)
        (coeffMatch279_6)]
      exact rowBound279_6 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨7, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨7, by decide⟩)
        (coeffMatch279_7)]
      exact rowBound279_7 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨8, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨8, by decide⟩)
        (coeffMatch279_8)]
      exact rowBound279_8 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨9, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨9, by decide⟩)
        (coeffMatch279_9)]
      exact rowBound279_9 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨10, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨10, by decide⟩)
        (coeffMatch279_10)]
      exact rowBound279_10 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨11, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨11, by decide⟩)
        (coeffMatch279_11)]
      exact rowBound279_11 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨12, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨12, by decide⟩)
        (coeffMatch279_12)]
      exact rowBound279_12 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨13, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨13, by decide⟩)
        (coeffMatch279_13)]
      exact rowBound279_13 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨14, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨14, by decide⟩)
        (coeffMatch279_14)]
      exact rowBound279_14 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨15, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨15, by decide⟩)
        (coeffMatch279_15)]
      exact rowBound279_15 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨16, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨16, by decide⟩)
        (coeffMatch279_16)]
      exact rowBound279_16 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨17, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨17, by decide⟩)
        (coeffMatch279_17)]
      exact rowBound279_17 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨18, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨18, by decide⟩)
        (coeffMatch279_18)]
      exact rowBound279_18 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨19, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨19, by decide⟩)
        (coeffMatch279_19)]
      exact rowBound279_19 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨20, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨20, by decide⟩)
        (coeffMatch279_20)]
      exact rowBound279_20 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨21, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨21, by decide⟩)
        (coeffMatch279_21)]
      exact rowBound279_21 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨22, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨22, by decide⟩)
        (coeffMatch279_22)]
      exact rowBound279_22 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨23, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨23, by decide⟩)
        (coeffMatch279_23)]
      exact rowBound279_23 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨24, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨24, by decide⟩)
        (coeffMatch279_24)]
      exact rowBound279_24 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨25, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨25, by decide⟩)
        (coeffMatch279_25)]
      exact rowBound279_25 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨26, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨26, by decide⟩)
        (coeffMatch279_26)]
      exact rowBound279_26 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨27, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨27, by decide⟩)
        (coeffMatch279_27)]
      exact rowBound279_27 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨28, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨28, by decide⟩)
        (coeffMatch279_28)]
      exact rowBound279_28 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨29, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨29, by decide⟩)
        (coeffMatch279_29)]
      exact rowBound279_29 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨30, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨30, by decide⟩)
        (coeffMatch279_30)]
      exact rowBound279_30 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨31, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨31, by decide⟩)
        (coeffMatch279_31)]
      exact rowBound279_31 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨32, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨32, by decide⟩)
        (coeffMatch279_32)]
      exact rowBound279_32 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨33, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨33, by decide⟩)
        (coeffMatch279_33)]
      exact rowBound279_33 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨34, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨34, by decide⟩)
        (coeffMatch279_34)]
      exact rowBound279_34 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨35, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨35, by decide⟩)
        (coeffMatch279_35)]
      exact rowBound279_35 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨36, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨36, by decide⟩)
        (coeffMatch279_36)]
      exact rowBound279_36 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨37, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨37, by decide⟩)
        (coeffMatch279_37)]
      exact rowBound279_37 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨38, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨38, by decide⟩)
        (coeffMatch279_38)]
      exact rowBound279_38 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨39, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨39, by decide⟩)
        (coeffMatch279_39)]
      exact rowBound279_39 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨40, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨40, by decide⟩)
        (coeffMatch279_40)]
      exact rowBound279_40 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨41, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨41, by decide⟩)
        (coeffMatch279_41)]
      exact rowBound279_41 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨42, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨42, by decide⟩)
        (coeffMatch279_42)]
      exact rowBound279_42 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨43, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨43, by decide⟩)
        (coeffMatch279_43)]
      exact rowBound279_43 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨44, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨44, by decide⟩)
        (coeffMatch279_44)]
      exact rowBound279_44 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨45, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨45, by decide⟩)
        (coeffMatch279_45)]
      exact rowBound279_45 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨46, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨46, by decide⟩)
        (coeffMatch279_46)]
      exact rowBound279_46 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨47, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨47, by decide⟩)
        (coeffMatch279_47)]
      exact rowBound279_47 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨48, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨48, by decide⟩)
        (coeffMatch279_48)]
      exact rowBound279_48 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨49, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨49, by decide⟩)
        (coeffMatch279_49)]
      exact rowBound279_49 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨50, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨50, by decide⟩)
        (coeffMatch279_50)]
      exact rowBound279_50 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨51, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨51, by decide⟩)
        (coeffMatch279_51)]
      exact rowBound279_51 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨52, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨52, by decide⟩)
        (coeffMatch279_52)]
      exact rowBound279_52 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨53, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨53, by decide⟩)
        (coeffMatch279_53)]
      exact rowBound279_53 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨54, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨54, by decide⟩)
        (coeffMatch279_54)]
      exact rowBound279_54 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨55, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨55, by decide⟩)
        (coeffMatch279_55)]
      exact rowBound279_55 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨56, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨56, by decide⟩)
        (coeffMatch279_56)]
      exact rowBound279_56 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨57, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨57, by decide⟩)
        (coeffMatch279_57)]
      exact rowBound279_57 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨58, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨58, by decide⟩)
        (coeffMatch279_58)]
      exact rowBound279_58 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨59, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨59, by decide⟩)
        (coeffMatch279_59)]
      exact rowBound279_59 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨60, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨60, by decide⟩)
        (coeffMatch279_60)]
      exact rowBound279_60 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨61, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨61, by decide⟩)
        (coeffMatch279_61)]
      exact rowBound279_61 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨62, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨62, by decide⟩)
        (coeffMatch279_62)]
      exact rowBound279_62 D
    · rw [weighted_sum_eq_filter_sum (S_279.occCoeff ⟨63, by decide⟩)
        (occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _))
        (activeSet279 ⟨63, by decide⟩)
        (coeffMatch279_63)]
      exact rowBound279_63 D
  hTotal := o279_total D
  hNonneg := fun j => occVectorInt_nonneg _ _ j

theorem step104_orbit279_lb17_split : QuotientRankAtLeast o279W 17 := by
  apply branchBridge_quotientRankAtLeast o279W 16 S_279
    orbit279_occupation_no_model
  intro r hr D
  by_cases hr16 : r < 16
  · exact False.elim ((step103_o279_base_lb16 r hr16).false D)
  · have hrr : r = 16 := by omega
    subst hrr
    exact ⟨_, o279_extractRootHolds_split D⟩

end QiushiMatmul
