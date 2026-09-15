import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace QiushiMatmul

/-- Reassemble bounded finite checks without changing their quantified domain. -/
theorem forall_fin_of_blocks {n blocks width : Nat}
    (hwidth : 0 < width) (hsize : n <= blocks * width)
    (P : Fin n -> Prop)
    (h : forall block : Fin blocks, forall offset : Fin width,
      forall hlt : block.val * width + offset.val < n,
        P (Fin.mk (block.val * width + offset.val) hlt)) :
    forall i : Fin n, P i := by
  intro i
  have hblock : i.val / width < blocks :=
    (Nat.div_lt_iff_lt_mul hwidth).2 (lt_of_lt_of_le i.isLt hsize)
  have hoffset : i.val % width < width := Nat.mod_lt _ hwidth
  have hid : i.val / width * width + i.val % width = i.val :=
    Nat.div_add_mod' _ _
  have hlt : i.val / width * width + i.val % width < n := by
    simpa only [hid] using i.isLt
  have result := h (Fin.mk _ hblock) (Fin.mk _ hoffset) hlt
  have heq : (Fin.mk (i.val / width * width + i.val % width) hlt) = i :=
    Fin.ext hid
  exact heq ▸ result

end QiushiMatmul
