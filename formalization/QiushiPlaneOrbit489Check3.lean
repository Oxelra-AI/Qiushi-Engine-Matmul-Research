import QiushiPlaneOrbit489Data

namespace QiushiMatmul.PlaneOrbit.Orbit489
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

theorem checked3 : ∀ j : Fin 128,
    data.RowOK (data.ix (384 + j.val)) := by decide +kernel +revert

end QiushiMatmul.PlaneOrbit.Orbit489
