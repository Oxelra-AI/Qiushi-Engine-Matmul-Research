import QiushiPlane482GenData
import QiushiCertifiedTransport
import QiushiBranch416Extraction
import QiushiMonoOrbit424From279
import QiushiMonoOrbit444From373
import QiushiWcOrbit290Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane482GenSource0010 :
    QuotientRankAtLeast (spanCodes [78, 26, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 10, 1] [(78, 11), (26, 257), (1, 1)]
    (codeMat 241) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit424_lb17_mono

theorem plane482GenSource0011 :
    QuotientRankAtLeast (spanCodes [66, 22, 12, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 10, 1] [(66, 69), (22, 42), (12, 11), (1, 1)]
    (codeMat 281) (codeMat 163) (codeMat 165) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit290_lb17_wc

theorem plane482GenSource0012 :
    QuotientRankAtLeast (spanCodes [72, 28, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 4, 1] [(72, 1), (28, 272), (1, 4)]
    (codeMat 86) (codeMat 275) (codeMat 275) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step113_orbit416_lb17

theorem plane482GenSource0013 :
    QuotientRankAtLeast (spanCodes [68, 16, 14, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 10, 1] [(68, 78), (16, 32), (14, 10), (1, 1)]
    (codeMat 401) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit290_lb17_wc

theorem plane482GenSource0014 :
    QuotientRankAtLeast (spanCodes [160, 84, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 84, 1] [(160, 160), (84, 84), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit444_lb17_mono

theorem plane482GenSource0015 :
    QuotientRankAtLeast (spanCodes [162, 84, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 84, 1] [(162, 160), (84, 85), (1, 1)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit444_lb17_mono

theorem plane482GenSource0016 :
    QuotientRankAtLeast (spanCodes [164, 84, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 84, 1] [(164, 245), (84, 85), (1, 1)]
    (codeMat 401) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit444_lb17_mono

theorem plane482GenSource0017 :
    QuotientRankAtLeast (spanCodes [166, 84, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 84, 1] [(166, 245), (84, 84), (1, 1)]
    (codeMat 465) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit444_lb17_mono

theorem plane482GenSource0018 :
    QuotientRankAtLeast (spanCodes [168, 84, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 84, 1] [(168, 160), (84, 85), (1, 1)]
    (codeMat 273) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit444_lb17_mono

theorem plane482GenSource0019 :
    QuotientRankAtLeast (spanCodes [170, 84, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 84, 1] [(170, 160), (84, 84), (1, 1)]
    (codeMat 337) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit444_lb17_mono

end QiushiMatmul
