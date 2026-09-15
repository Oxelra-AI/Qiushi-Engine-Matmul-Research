import QiushiFrozenRank365Data
import QiushiCertifiedTransport
import QiushiBranch262Dispatch
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiPlane152GenBindings00
import QiushiPlane315GenBindings01
import QiushiWcOrbit161Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane365RankCoverGenSource0020 :
    QuotientRankAtLeast (spanCodes [266, 130, 72, 34, 20, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(266, 409), (130, 438), (72, 2), (34, 284), (20, 316), (1, 3)]
    (codeMat 247) (codeMat 407) (codeMat 405) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.step113_262_row11_qr

theorem plane365RankCoverGenSource0021 :
    QuotientRankAtLeast (spanCodes [266, 130, 76, 34, 20, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(266, 465), (130, 1), (76, 283), (34, 366), (20, 222), (1, 192)]
    (codeMat 485) (codeMat 358) (codeMat 158) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.plane315GenBound0017

theorem plane365RankCoverGenSource0022 :
    QuotientRankAtLeast (spanCodes [266, 134, 76, 38, 20, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 68, 20, 10, 1] [(266, 465), (134, 356), (76, 180), (38, 319), (20, 228), (1, 288)]
    (codeMat 116) (codeMat 236) (codeMat 123) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.step109wc161s4Dispatch

theorem plane365RankCoverGenSource0023 :
    QuotientRankAtLeast (spanCodes [266, 134, 78, 38, 20, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 68, 20, 10, 1] [(266, 405), (134, 356), (78, 180), (38, 475), (20, 228), (1, 288)]
    (codeMat 117) (codeMat 492) (codeMat 115) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.step109wc161s4Dispatch

theorem plane365RankCoverGenSource0024 :
    QuotientRankAtLeast (spanCodes [266, 140, 70, 44, 20, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(266, 307), (140, 275), (70, 33), (44, 411), (20, 408), (1, 45)]
    (codeMat 372) (codeMat 409) (codeMat 473) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.step113_262_row11_qr

theorem plane365RankCoverGenSource0025 :
    QuotientRankAtLeast (spanCodes [266, 140, 72, 44, 20, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(266, 317), (140, 285), (72, 2), (44, 437), (20, 408), (1, 3)]
    (codeMat 375) (codeMat 417) (codeMat 177) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.step113_262_row11_qr

theorem plane365RankCoverGenSource0026 :
    QuotientRankAtLeast (spanCodes [266, 142, 76, 46, 20, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(266, 107), (142, 266), (76, 11), (46, 112), (20, 462), (1, 1)]
    (codeMat 369) (codeMat 167) (codeMat 167) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.plane152GenBound0001

theorem plane365RankCoverGenSource0027 :
    QuotientRankAtLeast (spanCodes [256, 160, 96, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 256), (160, 224), (96, 96), (20, 28), (8, 8), (2, 3), (1, 1)]
    (codeMat 273) (codeMat 275) (codeMat 275) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane365RankCoverGenSource0028 :
    QuotientRankAtLeast (spanCodes [256, 160, 100, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 360), (160, 245), (100, 96), (20, 30), (8, 9), (2, 3), (1, 1)]
    (codeMat 473) (codeMat 279) (codeMat 279) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane365RankCoverGenSource0029 :
    QuotientRankAtLeast (spanCodes [264, 128, 64, 32, 20, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(264, 160), (128, 8), (64, 16), (32, 256), (20, 68), (2, 1), (1, 2)]
    (codeMat 161) (codeMat 266) (codeMat 266) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
