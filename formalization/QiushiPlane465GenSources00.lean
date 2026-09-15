import QiushiPlane465GenData
import QiushiCertifiedTransport
import QiushiStep107Orbit373Extraction
import QiushiWcOrbit218Dispatch
import QiushiWcOrbit238Dispatch
import QiushiWcOrbit322Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane465GenSource0000 :
    QuotientRankAtLeast (spanCodes [289, 68, 17, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 160, 10, 1] [(289, 308), (68, 160), (17, 11), (10, 10)]
    (codeMat 267) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit322_lb17_wc

theorem plane465GenSource0001 :
    QuotientRankAtLeast (spanCodes [291, 68, 19, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [300, 224, 20, 1] [(291, 21), (68, 300), (19, 224), (10, 312)]
    (codeMat 207) (codeMat 342) (codeMat 215) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step107_orbit373_lb17

theorem plane465GenSource0002 :
    QuotientRankAtLeast (spanCodes [257, 68, 49, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 160, 10, 1] [(257, 11), (68, 10), (49, 308), (10, 170)]
    (codeMat 397) (codeMat 190) (codeMat 355) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit322_lb17_wc

theorem plane465GenSource0003 :
    QuotientRankAtLeast (spanCodes [261, 68, 53, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [300, 224, 20, 1] [(261, 224), (68, 312), (53, 21), (10, 20)]
    (codeMat 331) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step107_orbit373_lb17

theorem plane465GenSource0004 :
    QuotientRankAtLeast (spanCodes [304, 129, 68, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 160, 10, 1] [(304, 319), (129, 308), (68, 170), (10, 160)]
    (codeMat 143) (codeMat 428) (codeMat 107) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit322_lb17_wc

theorem plane465GenSource0005 :
    QuotientRankAtLeast (spanCodes [304, 135, 68, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [300, 224, 20, 1] [(304, 245), (135, 21), (68, 20), (10, 300)]
    (codeMat 461) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step107_orbit373_lb17

theorem plane465GenSource0006 :
    QuotientRankAtLeast (spanCodes [275, 130, 68, 35, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(275, 142), (130, 1), (68, 133), (35, 238), (10, 441)]
    (codeMat 309) (codeMat 335) (codeMat 426) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

theorem plane465GenSource0007 :
    QuotientRankAtLeast (spanCodes [277, 132, 68, 37, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(277, 473), (132, 434), (68, 435), (37, 349), (10, 97)]
    (codeMat 412) (codeMat 481) (codeMat 185) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

theorem plane465GenSource0008 :
    QuotientRankAtLeast (spanCodes [276, 133, 68, 36, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(276, 21), (133, 252), (68, 295), (36, 1), (10, 137)]
    (codeMat 275) (codeMat 95) (codeMat 244) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane465GenSource0009 :
    QuotientRankAtLeast (spanCodes [258, 147, 68, 50, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(258, 310), (147, 349), (68, 466), (50, 434), (10, 435)]
    (codeMat 314) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

end QiushiMatmul
