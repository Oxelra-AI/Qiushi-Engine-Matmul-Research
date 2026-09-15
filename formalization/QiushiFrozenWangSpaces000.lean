import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space0000_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [68, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(68, 68), (19, 19), (10, 10)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    det273 det273 inv273
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0000_lower : 18 ≤ frozenWangTable.L0 (spanCodes [68, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0000_orbit
  simpa only [lower450] using h

theorem space0001_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [69, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(69, 68), (19, 19), (10, 10)]
    (codeMat 273) (codeMat 277) (codeMat 277) false
    det273 det277 inv277
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0001_lower : 18 ≤ frozenWangTable.L0 (spanCodes [69, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0001_orbit
  simpa only [lower450] using h

theorem space0002_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [70, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(70, 68), (19, 19), (10, 10)]
    (codeMat 273) (codeMat 305) (codeMat 305) false
    det273 det305 inv305
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0002_lower : 18 ≤ frozenWangTable.L0 (spanCodes [70, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0002_orbit
  simpa only [lower450] using h

theorem space0003_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [71, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(71, 68), (19, 19), (10, 10)]
    (codeMat 273) (codeMat 309) (codeMat 309) false
    det273 det309 inv309
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0003_lower : 18 ≤ frozenWangTable.L0 (spanCodes [71, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0003_orbit
  simpa only [lower450] using h

theorem space0004_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [96, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(96, 68), (19, 19), (10, 25)]
    (codeMat 266) (codeMat 275) (codeMat 275) false
    det266 det275 inv275
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0004_lower : 18 ≤ frozenWangTable.L0 (spanCodes [96, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0004_orbit
  simpa only [lower450] using h

theorem space0005_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [97, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(97, 78), (19, 19), (10, 25)]
    (codeMat 266) (codeMat 307) (codeMat 311) false
    det266 det307 inv307
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0005_lower : 18 ≤ frozenWangTable.L0 (spanCodes [97, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0005_orbit
  simpa only [lower450] using h

theorem space0006_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [98, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(98, 93), (19, 19), (10, 25)]
    (codeMat 266) (codeMat 279) (codeMat 279) false
    det266 det279 inv279
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0006_lower : 18 ≤ frozenWangTable.L0 (spanCodes [98, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0006_orbit
  simpa only [lower450] using h

theorem space0007_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [99, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(99, 87), (19, 19), (10, 25)]
    (codeMat 266) (codeMat 311) (codeMat 307) false
    det266 det311 inv311
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0007_lower : 18 ≤ frozenWangTable.L0 (spanCodes [99, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0007_orbit
  simpa only [lower450] using h

theorem space0008_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [100, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(100, 68), (19, 10), (10, 25)]
    (codeMat 267) (codeMat 273) (codeMat 273) false
    det267 det273 inv273
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0008_lower : 18 ≤ frozenWangTable.L0 (spanCodes [100, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0008_orbit
  simpa only [lower450] using h

theorem space0009_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [101, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(101, 78), (19, 10), (10, 25)]
    (codeMat 267) (codeMat 305) (codeMat 305) false
    det267 det305 inv305
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0009_lower : 18 ≤ frozenWangTable.L0 (spanCodes [101, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0009_orbit
  simpa only [lower450] using h

theorem space0010_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [102, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(102, 87), (19, 10), (10, 25)]
    (codeMat 267) (codeMat 309) (codeMat 309) false
    det267 det309 inv309
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0010_lower : 18 ≤ frozenWangTable.L0 (spanCodes [102, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0010_orbit
  simpa only [lower450] using h

theorem space0011_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [103, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(103, 93), (19, 10), (10, 25)]
    (codeMat 267) (codeMat 277) (codeMat 277) false
    det267 det277 inv277
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0011_lower : 18 ≤ frozenWangTable.L0 (spanCodes [103, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0011_orbit
  simpa only [lower450] using h

theorem space0012_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [132, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(132, 68), (19, 10), (10, 25)]
    (codeMat 273) (codeMat 267) (codeMat 282) false
    det273 det267 inv267
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0012_lower : 18 ≤ frozenWangTable.L0 (spanCodes [132, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0012_orbit
  simpa only [lower450] using h

theorem space0013_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [133, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(133, 68), (19, 10), (10, 25)]
    (codeMat 273) (codeMat 303) (codeMat 286) false
    det273 det303 inv303
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0013_lower : 18 ≤ frozenWangTable.L0 (spanCodes [133, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0013_orbit
  simpa only [lower450] using h

theorem space0014_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [134, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(134, 68), (19, 10), (10, 25)]
    (codeMat 273) (codeMat 271) (codeMat 314) false
    det273 det271 inv271
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0014_lower : 18 ≤ frozenWangTable.L0 (spanCodes [134, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0014_orbit
  simpa only [lower450] using h

theorem space0015_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [135, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(135, 68), (19, 10), (10, 25)]
    (codeMat 273) (codeMat 299) (codeMat 318) false
    det273 det299 inv299
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0015_lower : 18 ≤ frozenWangTable.L0 (spanCodes [135, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0015_orbit
  simpa only [lower450] using h

theorem space0016_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [160, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(160, 68), (19, 25), (10, 10)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    det266 det266 inv266
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0016_lower : 18 ≤ frozenWangTable.L0 (spanCodes [160, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0016_orbit
  simpa only [lower450] using h

theorem space0017_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [161, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(161, 87), (19, 25), (10, 10)]
    (codeMat 266) (codeMat 302) (codeMat 302) false
    det266 det302 inv302
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0017_lower : 18 ≤ frozenWangTable.L0 (spanCodes [161, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0017_orbit
  simpa only [lower450] using h

theorem space0018_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [162, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(162, 78), (19, 25), (10, 10)]
    (codeMat 266) (codeMat 298) (codeMat 270) false
    det266 det298 inv298
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0018_lower : 18 ≤ frozenWangTable.L0 (spanCodes [162, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0018_orbit
  simpa only [lower450] using h

theorem space0019_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [163, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(163, 93), (19, 25), (10, 10)]
    (codeMat 266) (codeMat 270) (codeMat 298) false
    det266 det270 inv270
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0019_lower : 18 ≤ frozenWangTable.L0 (spanCodes [163, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0019_orbit
  simpa only [lower450] using h

theorem space0020_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [164, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(164, 68), (19, 25), (10, 19)]
    (codeMat 267) (codeMat 267) (codeMat 282) false
    det267 det267 inv267
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0020_lower : 18 ≤ frozenWangTable.L0 (spanCodes [164, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0020_orbit
  simpa only [lower450] using h

theorem space0021_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [165, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(165, 93), (19, 25), (10, 19)]
    (codeMat 267) (codeMat 271) (codeMat 314) false
    det267 det271 inv271
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0021_lower : 18 ≤ frozenWangTable.L0 (spanCodes [165, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0021_orbit
  simpa only [lower450] using h

theorem space0022_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [166, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(166, 78), (19, 25), (10, 19)]
    (codeMat 267) (codeMat 299) (codeMat 318) false
    det267 det299 inv299
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0022_lower : 18 ≤ frozenWangTable.L0 (spanCodes [166, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0022_orbit
  simpa only [lower450] using h

theorem space0023_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [167, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(167, 87), (19, 25), (10, 19)]
    (codeMat 267) (codeMat 303) (codeMat 286) false
    det267 det303 inv303
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0023_lower : 18 ≤ frozenWangTable.L0 (spanCodes [167, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0023_orbit
  simpa only [lower450] using h

theorem space0024_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [196, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(196, 68), (19, 25), (10, 19)]
    (codeMat 273) (codeMat 282) (codeMat 267) false
    det273 det282 inv282
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0024_lower : 18 ≤ frozenWangTable.L0 (spanCodes [196, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0024_orbit
  simpa only [lower450] using h

theorem space0025_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [197, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(197, 68), (19, 25), (10, 19)]
    (codeMat 273) (codeMat 314) (codeMat 271) false
    det273 det314 inv314
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0025_lower : 18 ≤ frozenWangTable.L0 (spanCodes [197, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0025_orbit
  simpa only [lower450] using h

theorem space0026_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [198, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(198, 68), (19, 25), (10, 19)]
    (codeMat 273) (codeMat 318) (codeMat 299) false
    det273 det318 inv318
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0026_lower : 18 ≤ frozenWangTable.L0 (spanCodes [198, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0026_orbit
  simpa only [lower450] using h

theorem space0027_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [199, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(199, 68), (19, 25), (10, 19)]
    (codeMat 273) (codeMat 286) (codeMat 303) false
    det273 det286 inv286
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0027_lower : 18 ≤ frozenWangTable.L0 (spanCodes [199, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0027_orbit
  simpa only [lower450] using h

theorem space0028_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [224, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(224, 68), (19, 10), (10, 19)]
    (codeMat 266) (codeMat 281) (codeMat 281) false
    det266 det281 inv281
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0028_lower : 18 ≤ frozenWangTable.L0 (spanCodes [224, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0028_orbit
  simpa only [lower450] using h

theorem space0029_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [225, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(225, 93), (19, 10), (10, 19)]
    (codeMat 266) (codeMat 285) (codeMat 317) false
    det266 det285 inv285
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0029_lower : 18 ≤ frozenWangTable.L0 (spanCodes [225, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0029_orbit
  simpa only [lower450] using h

theorem space0030_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [226, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(226, 87), (19, 10), (10, 19)]
    (codeMat 266) (codeMat 317) (codeMat 285) false
    det266 det317 inv317
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0030_lower : 18 ≤ frozenWangTable.L0 (spanCodes [226, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0030_orbit
  simpa only [lower450] using h

theorem space0031_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [227, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(227, 78), (19, 10), (10, 19)]
    (codeMat 266) (codeMat 313) (codeMat 313) false
    det266 det313 inv313
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0031_lower : 18 ≤ frozenWangTable.L0 (spanCodes [227, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0031_orbit
  simpa only [lower450] using h


end QiushiMatmul.FrozenWang
