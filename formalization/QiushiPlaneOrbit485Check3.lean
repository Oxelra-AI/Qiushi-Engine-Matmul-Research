import QiushiPlaneOrbit485Data

namespace QiushiMatmul.PlaneOrbit.Orbit485
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem checked3 : ∀ j : Fin 128,
    data.RowOK (data.ix (384 + j.val)) := by decide +kernel +revert

end QiushiMatmul.PlaneOrbit.Orbit485
