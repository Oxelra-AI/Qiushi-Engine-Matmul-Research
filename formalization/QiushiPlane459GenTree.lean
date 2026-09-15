import QiushiPlane459GenLeaf0000
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane459GenNoModel (x : Fin 28 → Int) (hroot : plane459GenOccSys.RootHolds x) : False := by
  exact plane459GenLeaf0000 x hroot

end QiushiMatmul
