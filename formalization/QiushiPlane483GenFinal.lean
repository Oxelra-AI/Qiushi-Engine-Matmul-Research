import QiushiPlane483GenBool
import QiushiPlane483GenTree
import QiushiPlane483GenDispatch
namespace QiushiMatmul

theorem plane483Gen_lb18 :
    QuotientRankAtLeast (spanCodes [160, 1]) 18 :=
  generic_plane_qra plane483GenConfig plane483GenBool plane483GenSourceQRA plane483GenDeadQRA
    (by decide) plane483GenNoModel

end QiushiMatmul
