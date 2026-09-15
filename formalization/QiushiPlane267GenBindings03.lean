import QiushiPlane267GenSources03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane267GenBound0030 :
    QuotientRankAtLeast (spanCodes (plane267GenSourceBasis (30 : Fin 33))) (plane267GenSourceLb (30 : Fin 33)) := by
  rw [show plane267GenSourceBasis (30 : Fin 33) = [256, 136, 80, 32, 4, 2, 1] from rfl,
      show plane267GenSourceLb (30 : Fin 33) = 9 from rfl]
  exact plane267GenSource0030
theorem plane267GenBound0031 :
    QuotientRankAtLeast (spanCodes (plane267GenSourceBasis (31 : Fin 33))) (plane267GenSourceLb (31 : Fin 33)) := by
  rw [show plane267GenSourceBasis (31 : Fin 33) = [272, 128, 80, 32, 4, 2, 1] from rfl,
      show plane267GenSourceLb (31 : Fin 33) = 9 from rfl]
  exact plane267GenSource0031
theorem plane267GenBound0032 :
    QuotientRankAtLeast (spanCodes (plane267GenSourceBasis (32 : Fin 33))) (plane267GenSourceLb (32 : Fin 33)) := by
  rw [show plane267GenSourceBasis (32 : Fin 33) = [280, 136, 80, 32, 4, 2, 1] from rfl,
      show plane267GenSourceLb (32 : Fin 33) = 9 from rfl]
  exact plane267GenSource0032
end QiushiMatmul
