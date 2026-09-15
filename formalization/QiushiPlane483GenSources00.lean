import QiushiPlane483GenData
import QiushiCertifiedTransport
import QiushiBranch416Extraction
import QiushiMonoOrbit423From279
import QiushiMonoOrbit424From279
import QiushiMonoOrbit431From279
import QiushiMonoOrbit440From373
import QiushiPlane282GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane483GenSource0000 :
    QuotientRankAtLeast (spanCodes [160, 2, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 4, 1] [(160, 272), (2, 4), (1, 1)]
    (codeMat 273) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step113_orbit416_lb17

theorem plane483GenSource0001 :
    QuotientRankAtLeast (spanCodes [160, 4, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 4, 1] [(160, 272), (4, 4), (1, 1)]
    (codeMat 161) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step113_orbit416_lb17

theorem plane483GenSource0002 :
    QuotientRankAtLeast (spanCodes [160, 6, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 4, 1] [(160, 272), (6, 4), (1, 1)]
    (codeMat 177) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step113_orbit416_lb17

theorem plane483GenSource0003 :
    QuotientRankAtLeast (spanCodes [160, 8, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 4, 1] [(160, 272), (8, 4), (1, 1)]
    (codeMat 161) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step113_orbit416_lb17

theorem plane483GenSource0004 :
    QuotientRankAtLeast (spanCodes [160, 10, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 10, 1] [(160, 160), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit423_lb17_mono

theorem plane483GenSource0005 :
    QuotientRankAtLeast (spanCodes [160, 16, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 10, 1] [(160, 10), (16, 1), (1, 256)]
    (codeMat 98) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit424_lb17_mono

theorem plane483GenSource0006 :
    QuotientRankAtLeast (spanCodes [160, 26, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [228, 16, 1] [(160, 228), (26, 17), (1, 16)]
    (codeMat 267) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit431_lb17_mono

theorem plane483GenSource0007 :
    QuotientRankAtLeast (spanCodes [160, 28, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [224, 20, 1] [(160, 224), (28, 20), (1, 1)]
    (codeMat 273) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit440_lb17_mono

theorem plane483GenSource0008 :
    QuotientRankAtLeast (spanCodes [160, 30, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [224, 20, 1] [(160, 224), (30, 20), (1, 1)]
    (codeMat 401) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit440_lb17_mono

theorem plane483GenSource0009 :
    QuotientRankAtLeast (spanCodes [132, 36, 12, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 10, 1] [(132, 280), (36, 27), (12, 26), (1, 16)]
    (codeMat 266) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane282Gen_lb17

end QiushiMatmul
