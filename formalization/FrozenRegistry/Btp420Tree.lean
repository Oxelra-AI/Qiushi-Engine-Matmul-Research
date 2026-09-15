import FrozenRegistry.Btp420Leaves000
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane420BtpGenNoModel (x : Fin 63 → Int) (hroot : plane420BtpGenOccSys.RootHolds x) : False := by
  exact plane420BtpGenLeaf0000 x hroot

end QiushiMatmul
