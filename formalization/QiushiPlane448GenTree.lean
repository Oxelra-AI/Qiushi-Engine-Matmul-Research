import QiushiPlane448GenLeaf0000
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane448GenNoModel (x : Fin 22 → Int) (hroot : plane448GenOccSys.RootHolds x) : False := by
  exact plane448GenLeaf0000 x hroot

end QiushiMatmul
