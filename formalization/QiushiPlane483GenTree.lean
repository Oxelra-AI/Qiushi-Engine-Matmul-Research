import QiushiPlane483GenLeaf0000
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane483GenNoModel (x : Fin 36 → Int) (hroot : plane483GenOccSys.RootHolds x) : False := by
  exact plane483GenLeaf0000 x hroot

end QiushiMatmul
