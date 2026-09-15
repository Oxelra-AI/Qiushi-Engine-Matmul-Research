import FrozenRegistry.Btp287Leaves000
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane287BtpGenNoModel (x : Fin 31 → Int) (hroot : plane287BtpGenOccSys.RootHolds x) : False := by
  exact plane287BtpGenLeaf0000 x hroot

end QiushiMatmul
