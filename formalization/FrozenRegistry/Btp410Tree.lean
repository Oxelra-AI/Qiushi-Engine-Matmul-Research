import FrozenRegistry.Btp410Leaves000
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane410BtpGenNoModel (x : Fin 63 → Int) (hroot : plane410BtpGenOccSys.RootHolds x) : False := by
  exact plane410BtpGenLeaf0000 x hroot

end QiushiMatmul
