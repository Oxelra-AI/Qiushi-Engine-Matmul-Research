import QiushiPlaneOrbit485Data

namespace QiushiMatmul.PlaneOrbit.Orbit485
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem checked9 : ∀ j : Fin 128,
    data.RowOK (data.ix (1152 + j.val)) := by decide +kernel +revert

end QiushiMatmul.PlaneOrbit.Orbit485
