import QiushiPlaneOrbit491Data

namespace QiushiMatmul.PlaneOrbit.Orbit491
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem checked0 : ∀ j : Fin 128,
    data.RowOK (data.ix (0 + j.val)) := by decide +kernel +revert

end QiushiMatmul.PlaneOrbit.Orbit491
