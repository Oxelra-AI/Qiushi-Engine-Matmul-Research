import QiushiPlane292GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit176From65
import QiushiMonoOrbit177From69
import QiushiStep128Mono158From72
import QiushiStep128Mono186From72
import QiushiWcOrbit157Dispatch
import QiushiWcOrbit179Dispatch
import QiushiWcOrbit180Dispatch
import QiushiWcOrbit187Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane292GenSource0000 :
    QuotientRankAtLeast (spanCodes [128, 32, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 20, 10, 1] [(128, 128), (32, 1), (20, 10), (10, 20), (1, 32)]
    (codeMat 266) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit157_lb15_wc

theorem plane292GenSource0001 :
    QuotientRankAtLeast (spanCodes [128, 32, 22, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [192, 32, 20, 10, 1] [(128, 192), (32, 32), (22, 31), (10, 11), (1, 1)]
    (codeMat 273) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit158_lb15_mono

theorem plane292GenSource0002 :
    QuotientRankAtLeast (spanCodes [128, 68, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 68, 32, 10, 1] [(128, 32), (68, 10), (32, 128), (10, 68), (1, 1)]
    (codeMat 161) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit176_lb15_mono

theorem plane292GenSource0003 :
    QuotientRankAtLeast (spanCodes [128, 70, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [144, 68, 32, 10, 1] [(128, 144), (70, 78), (32, 32), (10, 10), (1, 1)]
    (codeMat 401) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit177_lb15_mono

theorem plane292GenSource0004 :
    QuotientRankAtLeast (spanCodes [128, 80, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 20, 10, 1] [(128, 1), (80, 10), (32, 128), (10, 20), (1, 32)]
    (codeMat 84) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit157_lb15_wc

theorem plane292GenSource0005 :
    QuotientRankAtLeast (spanCodes [128, 82, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [192, 32, 20, 10, 1] [(128, 32), (82, 20), (32, 192), (10, 11), (1, 1)]
    (codeMat 281) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit158_lb15_mono

theorem plane292GenSource0006 :
    QuotientRankAtLeast (spanCodes [128, 84, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 84, 32, 10, 1] [(128, 128), (84, 84), (32, 32), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit179_lb15_wc

theorem plane292GenSource0007 :
    QuotientRankAtLeast (spanCodes [128, 86, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [144, 84, 32, 10, 1] [(128, 144), (86, 94), (32, 32), (10, 10), (1, 1)]
    (codeMat 401) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit180_lb15_wc

theorem plane292GenSource0008 :
    QuotientRankAtLeast (spanCodes [258, 128, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 128, 32, 10, 1] [(258, 264), (128, 32), (32, 1), (10, 258), (1, 128)]
    (codeMat 98) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit186_lb15_mono

theorem plane292GenSource0009 :
    QuotientRankAtLeast (spanCodes [262, 128, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(262, 262), (128, 128), (32, 32), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

end QiushiMatmul
