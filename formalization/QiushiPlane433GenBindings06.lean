import QiushiPlane433GenSources06
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane433GenBound0060 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (60 : Fin 63))) (plane433GenSourceLb (60 : Fin 63)) := by
  rw [show plane433GenSourceBasis (60 : Fin 63) = [258, 130, 96, 16, 10, 6, 1] from rfl,
      show plane433GenSourceLb (60 : Fin 63) = 12 from rfl]
  exact plane433GenSource0060
theorem plane433GenBound0061 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (61 : Fin 63))) (plane433GenSourceLb (61 : Fin 63)) := by
  rw [show plane433GenSourceBasis (61 : Fin 63) = [256, 132, 96, 16, 8, 2, 1] from rfl,
      show plane433GenSourceLb (61 : Fin 63) = 12 from rfl]
  exact plane433GenSource0061
theorem plane433GenBound0062 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (62 : Fin 63))) (plane433GenSourceLb (62 : Fin 63)) := by
  rw [show plane433GenSourceBasis (62 : Fin 63) = [256, 132, 64, 32, 16, 12, 2, 1] from rfl,
      show plane433GenSourceLb (62 : Fin 63) = 9 from rfl]
  exact plane433GenSource0062
end QiushiMatmul
