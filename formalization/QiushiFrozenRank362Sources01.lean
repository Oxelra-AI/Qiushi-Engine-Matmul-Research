import QiushiFrozenRank362Data
import QiushiCertifiedTransport
import QiushiOrbit14FP
import QiushiOrbit35FP
import QiushiPlane315GenBindings01
import QiushiWcOrbit78Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane362RankCoverGenSource0010 :
    QuotientRankAtLeast (spanCodes [264, 66, 32, 16, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(264, 20), (66, 96), (32, 2), (16, 128), (4, 1), (1, 8)]
    (codeMat 273) (codeMat 140) (codeMat 98) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit35_lb15

theorem plane362RankCoverGenSource0011 :
    QuotientRankAtLeast (spanCodes [256, 70, 32, 20, 8, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 130), (70, 119), (32, 2), (20, 22), (8, 1), (1, 9)]
    (codeMat 410) (codeMat 161) (codeMat 161) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit35_lb15

theorem plane362RankCoverGenSource0012 :
    QuotientRankAtLeast (spanCodes [290, 134, 102, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(290, 452), (134, 223), (102, 117), (20, 31), (10, 11), (1, 1)]
    (codeMat 465) (codeMat 311) (codeMat 307) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.plane315GenBound0017

theorem plane362RankCoverGenSource0013 :
    QuotientRankAtLeast (spanCodes [292, 162, 102, 20, 12, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 96, 20, 10, 1] [(292, 1), (162, 129), (102, 254), (20, 138), (12, 268), (1, 365)]
    (codeMat 351) (codeMat 87) (codeMat 468) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.step109_orbit78_lb14_wc

theorem plane362RankCoverGenSource0014 :
    QuotientRankAtLeast (spanCodes [294, 130, 102, 20, 14, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 96, 20, 10, 1] [(294, 371), (130, 504), (102, 499), (20, 269), (14, 97), (1, 365)]
    (codeMat 163) (codeMat 253) (codeMat 415) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.step109_orbit78_lb14_wc

theorem plane362RankCoverGenSource0015 :
    QuotientRankAtLeast (spanCodes [294, 134, 102, 20, 14, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 96, 20, 10, 1] [(294, 10), (134, 21), (102, 498), (20, 20), (14, 274), (1, 128)]
    (codeMat 143) (codeMat 98) (codeMat 140) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.step109_orbit78_lb14_wc

theorem plane362RankCoverGenSource0016 :
    QuotientRankAtLeast (spanCodes [266, 128, 68, 34, 20, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 96, 20, 10, 1] [(266, 159), (128, 390), (68, 97), (34, 402), (20, 274), (1, 365)]
    (codeMat 239) (codeMat 465) (codeMat 465) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.step109_orbit78_lb14_wc

theorem plane362RankCoverGenSource0017 :
    QuotientRankAtLeast (spanCodes [266, 136, 68, 34, 20, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 96, 20, 10, 1] [(266, 244), (136, 11), (68, 274), (34, 224), (20, 280), (1, 128)]
    (codeMat 86) (codeMat 282) (codeMat 267) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.step109_orbit78_lb14_wc

theorem plane362RankCoverGenSource0018 :
    QuotientRankAtLeast (spanCodes [258, 128, 76, 42, 20, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(258, 97), (128, 260), (76, 11), (42, 126), (20, 463), (1, 1)]
    (codeMat 313) (codeMat 163) (codeMat 165) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.plane315GenBound0017

theorem plane362RankCoverGenSource0019 :
    QuotientRankAtLeast (spanCodes [292, 128, 100, 20, 12, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(292, 360), (128, 128), (100, 232), (20, 23), (12, 30), (2, 2), (1, 3)]
    (codeMat 281) (codeMat 285) (codeMat 317) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
