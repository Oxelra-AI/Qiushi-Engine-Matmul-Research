import QiushiPlane292GenLeaf0000
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane292GenNoModel (x : Fin 11 → Int) (hroot : plane292GenOccSys.RootHolds x) : False := by
  exact plane292GenLeaf0000 x hroot

end QiushiMatmul
