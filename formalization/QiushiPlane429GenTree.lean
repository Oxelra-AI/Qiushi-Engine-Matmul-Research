import QiushiPlane429GenLeaf0000
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane429GenNoModel (x : Fin 61 → Int) (hroot : plane429GenOccSys.RootHolds x) : False := by
  exact plane429GenLeaf0000 x hroot

end QiushiMatmul
