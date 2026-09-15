import QiushiDefs

/-!
# Finite-premise surface for the Qiushi lower-bound proof

All fields are actual quotient-rank propositions about named A-slot subspaces.
Inhabiting `FinitePremises` is the finite certificate obligation; no field is a
`True` placeholder.
-/

open Matrix BigOperators

namespace QiushiMatmul

/-- Representative A-slot lines: rank 1, rank 2, rank 3. -/
def lineRank1 : Submodule F2 Mat3 := spanCodes [1]
def lineRank2 : Submodule F2 Mat3 := spanCodes [17]
def lineRank3 : Submodule F2 Mat3 := spanCodes [273]

/-- Eight all-high two-plane representatives 484--491. -/
def plane484 : Submodule F2 Mat3 := spanCodes [19,10]
def plane485 : Submodule F2 Mat3 := spanCodes [20,10]
def plane486 : Submodule F2 Mat3 := spanCodes [68,10]
def plane487 : Submodule F2 Mat3 := spanCodes [84,10]
def plane488 : Submodule F2 Mat3 := spanCodes [96,10]
def plane489 : Submodule F2 Mat3 := spanCodes [258,10]
def plane490 : Submodule F2 Mat3 := spanCodes [275,10]
def plane491 : Submodule F2 Mat3 := spanCodes [163,84]

/-- Normalized affine column-coset span `S=<272,4,2,1>`.
Kept as a name for the geometry discussion; it is not a field of the final
finite-premise interface because the profile argument only consumes the fourteen
affine-plane hyperplane bounds. -/
def normalizedCosetSpan : Submodule F2 Mat3 := spanCodes [272,4,2,1]

/-- Rank-one first-row family `R=<4,2,1>`.
Kept as a name for reference; the final profile forcing does not consume its
quotient-rank bound. -/
def firstRowFamily : Submodule F2 Mat3 := spanCodes [4,2,1]

/-- The fourteen affine-plane hyperplanes in `S`, from the checked finite bundle. -/
def affineHyperplane0  : Submodule F2 Mat3 := spanCodes [272,4,2]
def affineHyperplane1  : Submodule F2 Mat3 := spanCodes [273,4,2]
def affineHyperplane2  : Submodule F2 Mat3 := spanCodes [272,4,1]
def affineHyperplane3  : Submodule F2 Mat3 := spanCodes [274,4,1]
def affineHyperplane4  : Submodule F2 Mat3 := spanCodes [272,4,3]
def affineHyperplane5  : Submodule F2 Mat3 := spanCodes [273,4,3]
def affineHyperplane6  : Submodule F2 Mat3 := spanCodes [272,2,1]
def affineHyperplane7  : Submodule F2 Mat3 := spanCodes [276,2,1]
def affineHyperplane8  : Submodule F2 Mat3 := spanCodes [272,5,2]
def affineHyperplane9  : Submodule F2 Mat3 := spanCodes [273,5,2]
def affineHyperplane10 : Submodule F2 Mat3 := spanCodes [272,6,1]
def affineHyperplane11 : Submodule F2 Mat3 := spanCodes [274,6,1]
def affineHyperplane12 : Submodule F2 Mat3 := spanCodes [272,5,3]
def affineHyperplane13 : Submodule F2 Mat3 := spanCodes [273,5,3]

def affineHyperplane (i : Fin 14) : Submodule F2 Mat3 :=
  match i.val with
  | 0 => affineHyperplane0
  | 1 => affineHyperplane1
  | 2 => affineHyperplane2
  | 3 => affineHyperplane3
  | 4 => affineHyperplane4
  | 5 => affineHyperplane5
  | 6 => affineHyperplane6
  | 7 => affineHyperplane7
  | 8 => affineHyperplane8
  | 9 => affineHyperplane9
  | 10 => affineHyperplane10
  | 11 => affineHyperplane11
  | 12 => affineHyperplane12
  | _ => affineHyperplane13

/-- Exact finite premises consumed by the symbolic proof. -/
structure FinitePremises where
  line_rank1_lb19 : QuotientRankAtLeast lineRank1 19
  line_rank2_lb19 : QuotientRankAtLeast lineRank2 19
  line_rank3_lb19 : QuotientRankAtLeast lineRank3 19
  plane484_lb19 : QuotientRankAtLeast plane484 19
  plane485_lb19 : QuotientRankAtLeast plane485 19
  plane486_lb19 : QuotientRankAtLeast plane486 19
  plane487_lb19 : QuotientRankAtLeast plane487 19
  plane488_lb19 : QuotientRankAtLeast plane488 19
  plane489_lb19 : QuotientRankAtLeast plane489 19
  plane490_lb19 : QuotientRankAtLeast plane490 19
  plane491_lb19 : QuotientRankAtLeast plane491 19
  affine_hyperplane_lb17 : ∀ i : Fin 14, QuotientRankAtLeast (affineHyperplane i) 17

end QiushiMatmul
