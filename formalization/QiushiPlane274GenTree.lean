import QiushiPlane274GenLeaf0000
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane274GenNoModel (x : Fin 21 → Int) (hroot : plane274GenOccSys.RootHolds x) : False := by
  exact plane274GenLeaf0000 x hroot

end QiushiMatmul
