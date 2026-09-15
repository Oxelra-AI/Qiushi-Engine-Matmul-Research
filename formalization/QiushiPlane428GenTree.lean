import QiushiPlane428GenLeaf0000
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane428GenNoModel (x : Fin 36 → Int) (hroot : plane428GenOccSys.RootHolds x) : False := by
  exact plane428GenLeaf0000 x hroot

end QiushiMatmul
