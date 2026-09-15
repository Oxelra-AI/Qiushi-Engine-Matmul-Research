import FrozenRegistry.Btp227Data
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiPlane269GenBindings01
import QiushiStep99Orbit68Dispatch
import QiushiWcOrbit127Dispatch
import QiushiWcOrbit202Dispatch
import QiushiWcOrbit204Dispatch
import QiushiWcOrbit78Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane227BtpGenSource0000 :
    QuotientRankAtLeast (spanCodes [292, 140, 96, 16, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(292, 511), (140, 93), (96, 252), (16, 9), (2, 1), (1, 3)]
    (codeMat 345) (codeMat 303) (codeMat 286) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane227BtpGenSource0001 :
    QuotientRankAtLeast (spanCodes [290, 136, 96, 16, 4, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 96, 12, 2, 1] [(290, 133), (136, 231), (96, 139), (16, 504), (4, 2), (1, 3)]
    (codeMat 489) (codeMat 187) (codeMat 229) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109wc127s0Dispatch

theorem plane227BtpGenSource0002 :
    QuotientRankAtLeast (spanCodes [288, 138, 96, 16, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 148, 80, 32, 8, 2, 1] [(288, 438), (138, 189), (96, 406), (16, 455), (6, 1), (1, 2)]
    (codeMat 225) (codeMat 442) (codeMat 334) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269GenBound0016

theorem plane227BtpGenSource0003 :
    QuotientRankAtLeast (spanCodes [294, 132, 96, 16, 8, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 68, 8, 2, 1] [(294, 381), (132, 168), (96, 69), (16, 2), (8, 1), (1, 8)]
    (codeMat 266) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109wc202s9Dispatch

theorem plane227BtpGenSource0004 :
    QuotientRankAtLeast (spanCodes [294, 134, 96, 16, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 164, 68, 16, 10, 1] [(294, 404), (134, 164), (96, 240), (16, 16), (10, 10), (1, 27)]
    (codeMat 275) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit68_lb14_unconditional

theorem plane227BtpGenSource0005 :
    QuotientRankAtLeast (spanCodes [294, 128, 96, 16, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 148, 80, 32, 8, 2, 1] [(294, 35), (128, 1), (96, 83), (16, 2), (12, 189), (1, 455)]
    (codeMat 468) (codeMat 103) (codeMat 188) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269GenBound0016

theorem plane227BtpGenSource0006 :
    QuotientRankAtLeast (spanCodes [294, 130, 96, 16, 14, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 96, 12, 2, 1] [(294, 15), (130, 2), (96, 368), (16, 3), (14, 231), (1, 504)]
    (codeMat 239) (codeMat 106) (codeMat 396) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109wc127s0Dispatch

theorem plane227BtpGenSource0007 :
    QuotientRankAtLeast (spanCodes [262, 140, 64, 32, 16, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 148, 80, 32, 8, 2, 1] [(262, 80), (140, 156), (64, 32), (32, 2), (16, 3), (1, 256)]
    (codeMat 98) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269GenBound0016

theorem plane227BtpGenSource0008 :
    QuotientRankAtLeast (spanCodes [260, 140, 66, 34, 16, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [274, 144, 68, 32, 10, 1] [(260, 455), (140, 460), (66, 306), (34, 280), (16, 32), (1, 144)]
    (codeMat 214) (codeMat 428) (codeMat 107) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109wc204s4Dispatch

theorem plane227BtpGenSource0009 :
    QuotientRankAtLeast (spanCodes [258, 140, 68, 36, 16, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 96, 20, 10, 1] [(258, 20), (140, 117), (68, 11), (36, 128), (16, 390), (1, 1)]
    (codeMat 233) (codeMat 177) (codeMat 417) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit78_lb14_wc

end QiushiMatmul
