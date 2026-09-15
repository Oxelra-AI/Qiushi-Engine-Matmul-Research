import QiushiPlane483GenData
import QiushiCertifiedTransport
import QiushiBranch416Extraction
import QiushiMonoOrbit423From279
import QiushiMonoOrbit440From373
import QiushiMonoOrbit442From373
import QiushiMonoOrbit443From373
import QiushiPlane282GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane483GenSource0010 :
    QuotientRankAtLeast (spanCodes [138, 42, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 20, 1] [(138, 264), (42, 20), (1, 1)]
    (codeMat 337) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit442_lb17_mono

theorem plane483GenSource0011 :
    QuotientRankAtLeast (spanCodes [142, 46, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 20, 1] [(142, 266), (46, 21), (1, 1)]
    (codeMat 345) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit443_lb17_mono

theorem plane483GenSource0012 :
    QuotientRankAtLeast (spanCodes [150, 54, 14, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 10, 1] [(150, 280), (54, 27), (14, 26), (1, 16)]
    (codeMat 394) (codeMat 428) (codeMat 107) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane282Gen_lb17

theorem plane483GenSource0013 :
    QuotientRankAtLeast (spanCodes [154, 58, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 20, 1] [(154, 264), (58, 20), (1, 1)]
    (codeMat 465) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit442_lb17_mono

theorem plane483GenSource0014 :
    QuotientRankAtLeast (spanCodes [156, 60, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 20, 1] [(156, 266), (60, 21), (1, 1)]
    (codeMat 473) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit443_lb17_mono

theorem plane483GenSource0015 :
    QuotientRankAtLeast (spanCodes [160, 64, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 4, 1] [(160, 272), (64, 4), (1, 1)]
    (codeMat 273) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step113_orbit416_lb17

theorem plane483GenSource0016 :
    QuotientRankAtLeast (spanCodes [160, 68, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 10, 1] [(160, 160), (68, 10), (1, 1)]
    (codeMat 161) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit423_lb17_mono

theorem plane483GenSource0017 :
    QuotientRankAtLeast (spanCodes [160, 72, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 4, 1] [(160, 272), (72, 4), (1, 1)]
    (codeMat 401) (codeMat 417) (codeMat 177) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step113_orbit416_lb17

theorem plane483GenSource0018 :
    QuotientRankAtLeast (spanCodes [160, 78, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 10, 1] [(160, 160), (78, 10), (1, 1)]
    (codeMat 177) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit423_lb17_mono

theorem plane483GenSource0019 :
    QuotientRankAtLeast (spanCodes [160, 82, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [224, 20, 1] [(160, 224), (82, 20), (1, 1)]
    (codeMat 281) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit440_lb17_mono

end QiushiMatmul
