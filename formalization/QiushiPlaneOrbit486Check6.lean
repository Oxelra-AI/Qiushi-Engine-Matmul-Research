import QiushiPlaneOrbit486Data

namespace QiushiMatmul.PlaneOrbit.Orbit486
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem checked6 : ∀ j : Fin 128,
    data.RowOK (data.ix (768 + j.val)) := by decide +kernel +revert

end QiushiMatmul.PlaneOrbit.Orbit486
