import QiushiPlane433GenLeaf0000
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane433GenNoModel (x : Fin 31 → Int) (hroot : plane433GenOccSys.RootHolds x) : False := by
  exact plane433GenLeaf0000 x hroot

end QiushiMatmul
