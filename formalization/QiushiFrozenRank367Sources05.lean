import QiushiFrozenRank367Data
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane367RankCoverGenSource0050 :
    QuotientRankAtLeast (spanCodes [262, 128, 70, 32, 20, 8, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 255), (128, 256), (70, 127), (32, 3), (20, 31), (8, 1), (1, 9)]
    (codeMat 282) (codeMat 165) (codeMat 163) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane367RankCoverGenSource0051 :
    QuotientRankAtLeast (spanCodes [262, 130, 68, 34, 20, 8, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 413), (130, 360), (68, 119), (34, 29), (20, 30), (8, 8), (1, 9)]
    (codeMat 467) (codeMat 419) (codeMat 183) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane367RankCoverGenSource0052 :
    QuotientRankAtLeast (spanCodes [262, 132, 70, 36, 20, 8, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 414), (132, 373), (70, 30), (36, 130), (20, 138), (8, 1), (1, 3)]
    (codeMat 474) (codeMat 407) (codeMat 405) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane367RankCoverGenSource0053 :
    QuotientRankAtLeast (spanCodes [260, 130, 68, 34, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 8), (130, 9), (68, 264), (34, 29), (20, 30), (10, 413), (1, 360)]
    (codeMat 309) (codeMat 122) (codeMat 460) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane367RankCoverGenSource0054 :
    QuotientRankAtLeast (spanCodes [260, 134, 64, 38, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 3), (134, 28), (64, 8), (38, 252), (20, 483), (10, 119), (1, 9)]
    (codeMat 421) (codeMat 183) (codeMat 419) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane367RankCoverGenSource0055 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 32, 20, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 276), (128, 130), (64, 128), (32, 8), (20, 97), (12, 96), (1, 256)]
    (codeMat 98) (codeMat 226) (codeMat 141) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane367RankCoverGenSource0056 :
    QuotientRankAtLeast (spanCodes [258, 128, 68, 32, 20, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 284), (128, 511), (68, 480), (32, 8), (20, 105), (12, 96), (1, 256)]
    (codeMat 122) (codeMat 242) (codeMat 205) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane367RankCoverGenSource0057 :
    QuotientRankAtLeast (spanCodes [258, 130, 68, 34, 20, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 353), (130, 360), (68, 278), (34, 97), (20, 105), (12, 406), (1, 130)]
    (codeMat 415) (codeMat 394) (codeMat 330) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane367RankCoverGenSource0058 :
    QuotientRankAtLeast (spanCodes [258, 132, 64, 36, 20, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 148), (132, 150), (64, 384), (36, 360), (20, 361), (12, 352), (1, 256)]
    (codeMat 106) (codeMat 498) (codeMat 206) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane367RankCoverGenSource0059 :
    QuotientRankAtLeast (spanCodes [258, 132, 70, 36, 20, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 168), (132, 184), (70, 495), (36, 256), (20, 264), (12, 257), (1, 325)]
    (codeMat 234) (codeMat 465) (codeMat 465) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
