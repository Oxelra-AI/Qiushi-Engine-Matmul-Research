import QiushiPlane455GenData
import QiushiCertifiedTransport
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit236Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane455GenSource0020 :
    QuotientRankAtLeast (spanCodes [129, 70, 34, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(129, 175), (70, 497), (34, 10), (20, 11), (10, 42)]
    (codeMat 403) (codeMat 125) (codeMat 348) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane455GenSource0021 :
    QuotientRankAtLeast (spanCodes [257, 129, 37, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(257, 496), (129, 497), (37, 464), (20, 42), (10, 175)]
    (codeMat 468) (codeMat 122) (codeMat 460) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane455GenSource0022 :
    QuotientRankAtLeast (spanCodes [291, 129, 99, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(291, 164), (129, 497), (99, 165), (20, 373), (10, 350)]
    (codeMat 500) (codeMat 494) (codeMat 501) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane455GenSource0023 :
    QuotientRankAtLeast (spanCodes [292, 129, 100, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(292, 1), (129, 228), (100, 505), (20, 132), (10, 402)]
    (codeMat 87) (codeMat 205) (codeMat 242) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane455GenSource0024 :
    QuotientRankAtLeast (spanCodes [260, 129, 69, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(260, 1), (129, 42), (69, 11), (20, 497), (10, 175)]
    (codeMat 421) (codeMat 158) (codeMat 358) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane455GenSource0025 :
    QuotientRankAtLeast (spanCodes [288, 129, 97, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(288, 504), (129, 132), (97, 381), (20, 228), (10, 402)]
    (codeMat 124) (codeMat 428) (codeMat 107) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane455GenSource0026 :
    QuotientRankAtLeast (spanCodes [291, 129, 102, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(291, 383), (129, 363), (102, 382), (20, 276), (10, 373)]
    (codeMat 477) (codeMat 185) (codeMat 481) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane455GenSource0027 :
    QuotientRankAtLeast (spanCodes [288, 129, 102, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(288, 1), (129, 373), (102, 340), (20, 497), (10, 350)]
    (codeMat 494) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane455GenSource0028 :
    QuotientRankAtLeast (spanCodes [293, 129, 99, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(293, 126), (129, 276), (99, 106), (20, 363), (10, 373)]
    (codeMat 358) (codeMat 499) (codeMat 382) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane455GenSource0029 :
    QuotientRankAtLeast (spanCodes [295, 129, 97, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 136, 96, 20, 1] [(295, 263), (129, 136), (97, 398), (20, 371), (10, 232)]
    (codeMat 421) (codeMat 412) (codeMat 111) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit236_lb16_wc

end QiushiMatmul
