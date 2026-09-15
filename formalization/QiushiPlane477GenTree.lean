import QiushiPlane477GenLeaf0000
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane477GenNoModel (x : Fin 0 → Int) (hroot : plane477GenOccSys.RootHolds x) : False := by
  exact plane477GenLeaf0000 x hroot

end QiushiMatmul
