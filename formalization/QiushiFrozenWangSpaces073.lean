import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space2336_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [276, 84, 54, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(276, 160), (84, 161), (54, 260), (10, 430)]
    (codeMat 468) (codeMat 185) (codeMat 481) false
    det468 det185 inv185
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2336_lower : 17 ≤ frozenWangTable.L0 (spanCodes [276, 84, 54, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2336_orbit
  simpa only [lower315] using h

theorem space2337_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [273, 84, 50, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(273, 270), (84, 271), (50, 170), (10, 430)]
    (codeMat 477) (codeMat 171) (codeMat 485) false
    det477 det171 inv171
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2337_lower : 17 ≤ frozenWangTable.L0 (spanCodes [273, 84, 50, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2337_orbit
  simpa only [lower315] using h

theorem space2338_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [256, 84, 48, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(256, 1), (84, 271), (48, 260), (10, 430)]
    (codeMat 412) (codeMat 143) (codeMat 482) false
    det412 det143 inv143
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2338_lower : 17 ≤ frozenWangTable.L0 (spanCodes [256, 84, 48, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2338_orbit
  simpa only [lower315] using h

theorem space2339_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [288, 68, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(288, 260), (68, 160), (16, 1), (10, 10)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    det266 det266 inv266
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2339_lower : 17 ≤ frozenWangTable.L0 (spanCodes [288, 68, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2339_orbit
  simpa only [lower315] using h

theorem space2340_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [260, 84, 53, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(260, 1), (84, 161), (53, 170), (10, 430)]
    (codeMat 405) (codeMat 157) (codeMat 486) false
    det405 det157 inv157
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2340_lower : 17 ≤ frozenWangTable.L0 (spanCodes [260, 84, 53, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2340_orbit
  simpa only [lower315] using h

theorem space2341_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [288, 69, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(288, 260), (69, 160), (17, 11), (10, 10)]
    (codeMat 331) (codeMat 282) (codeMat 267) false
    det331 det282 inv282
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2341_lower : 17 ≤ frozenWangTable.L0 (spanCodes [288, 69, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2341_orbit
  simpa only [lower315] using h

theorem space2342_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [260, 134, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(260, 1), (134, 11), (84, 171), (10, 420)]
    (codeMat 229) (codeMat 92) (codeMat 116) false
    det229 det92 inv92
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2342_lower : 17 ≤ frozenWangTable.L0 (spanCodes [260, 134, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2342_orbit
  simpa only [lower315] using h

theorem space2343_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [273, 146, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(273, 270), (146, 260), (84, 271), (10, 420)]
    (codeMat 165) (codeMat 492) (codeMat 115) false
    det165 det492 inv492
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2343_lower : 17 ≤ frozenWangTable.L0 (spanCodes [273, 146, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2343_orbit
  simpa only [lower315] using h

theorem space2344_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [256, 144, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(256, 1), (144, 260), (84, 271), (10, 420)]
    (codeMat 172) (codeMat 204) (codeMat 114) false
    det172 det204 inv204
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2344_lower : 17 ≤ frozenWangTable.L0 (spanCodes [256, 144, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2344_orbit
  simpa only [lower315] using h

theorem space2345_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [276, 133, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(276, 170), (133, 11), (84, 171), (10, 420)]
    (codeMat 236) (codeMat 380) (codeMat 117) false
    det236 det380 inv380
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2345_lower : 17 ≤ frozenWangTable.L0 (spanCodes [276, 133, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2345_orbit
  simpa only [lower315] using h

theorem space2346_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [384, 69, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(384, 260), (69, 170), (17, 11), (10, 10)]
    (codeMat 459) (codeMat 318) (codeMat 299) false
    det459 det318 inv318
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2346_lower : 17 ≤ frozenWangTable.L0 (spanCodes [384, 69, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2346_orbit
  simpa only [lower315] using h

theorem space2347_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [386, 69, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(386, 430), (69, 170), (17, 11), (10, 10)]
    (codeMat 395) (codeMat 286) (codeMat 303) false
    det395 det286 inv286
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2347_lower : 17 ≤ frozenWangTable.L0 (spanCodes [386, 69, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2347_orbit
  simpa only [lower315] using h

theorem space2348_orbit :
    frozenWangTable.OrbitImage 448 (spanCodes [404, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 448 [(404, 315), (84, 314), (10, 160)]
    (codeMat 140) (codeMat 428) (codeMat 107) false
    det140 det428 inv428
    (by rw [basis448]; decide +kernel)
    (by rw [basis448]; decide +kernel)

theorem space2348_lower : 17 ≤ frozenWangTable.L0 (spanCodes [404, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 448 space2348_orbit
  simpa only [lower448] using h

theorem space2349_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [291, 130, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(291, 10), (130, 260), (84, 171), (10, 420)]
    (codeMat 183) (codeMat 236) (codeMat 123) false
    det183 det236 inv236
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2349_lower : 17 ≤ frozenWangTable.L0 (spanCodes [291, 130, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2349_orbit
  simpa only [lower315] using h

theorem space2350_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [387, 84, 34, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(387, 420), (84, 161), (34, 170), (10, 430)]
    (codeMat 351) (codeMat 431) (codeMat 477) false
    det351 det431 inv431
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2350_lower : 17 ≤ frozenWangTable.L0 (spanCodes [387, 84, 34, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2350_orbit
  simpa only [lower315] using h

theorem space2351_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [305, 151, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(305, 161), (151, 11), (84, 271), (10, 420)]
    (codeMat 254) (codeMat 348) (codeMat 125) false
    det254 det348 inv348
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2351_lower : 17 ≤ frozenWangTable.L0 (spanCodes [305, 151, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2351_orbit
  simpa only [lower315] using h

theorem space2352_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [386, 84, 36, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(386, 420), (84, 271), (36, 260), (10, 430)]
    (codeMat 342) (codeMat 409) (codeMat 473) false
    det342 det409 inv409
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2352_lower : 17 ≤ frozenWangTable.L0 (spanCodes [386, 84, 36, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2352_orbit
  simpa only [lower315] using h

theorem space2353_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [304, 128, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(304, 261), (128, 260), (84, 171), (10, 420)]
    (codeMat 190) (codeMat 460) (codeMat 122) false
    det190 det460 inv460
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2353_lower : 17 ≤ frozenWangTable.L0 (spanCodes [304, 128, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2353_orbit
  simpa only [lower315] using h

theorem space2354_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [400, 84, 32, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(400, 261), (84, 161), (32, 260), (10, 430)]
    (codeMat 286) (codeMat 395) (codeMat 474) false
    det286 det395 inv395
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2354_lower : 17 ≤ frozenWangTable.L0 (spanCodes [400, 84, 32, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2354_orbit
  simpa only [lower315] using h

theorem space2355_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [290, 148, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(290, 10), (148, 11), (84, 271), (10, 420)]
    (codeMat 247) (codeMat 124) (codeMat 124) false
    det247 det124 inv124
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2355_lower : 17 ≤ frozenWangTable.L0 (spanCodes [290, 148, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2355_orbit
  simpa only [lower315] using h

theorem space2356_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [401, 84, 39, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(401, 171), (84, 271), (39, 170), (10, 430)]
    (codeMat 279) (codeMat 445) (codeMat 478) false
    det279 det445 inv445
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2356_lower : 17 ≤ frozenWangTable.L0 (spanCodes [401, 84, 39, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2356_orbit
  simpa only [lower315] using h

theorem space2357_orbit :
    frozenWangTable.OrbitImage 254 (spanCodes [84, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 254 [(84, 84), (8, 8), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    det273 det273 inv273
    (by rw [basis254]; decide +kernel)
    (by rw [basis254]; decide +kernel)

theorem space2357_lower : 16 ≤ frozenWangTable.L0 (spanCodes [84, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 254 space2357_orbit
  simpa only [lower254] using h

theorem space2358_orbit :
    frozenWangTable.OrbitImage 269 (spanCodes [80, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 269 [(80, 264), (8, 32), (4, 2), (2, 1)]
    (codeMat 273) (codeMat 98) (codeMat 140) false
    det273 det98 inv98
    (by rw [basis269]; decide +kernel)
    (by rw [basis269]; decide +kernel)

theorem space2358_lower : 16 ≤ frozenWangTable.L0 (spanCodes [80, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 269 space2358_orbit
  simpa only [lower269] using h

theorem space2359_orbit :
    frozenWangTable.OrbitImage 269 (spanCodes [81, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 269 [(81, 297), (9, 32), (5, 2), (3, 1)]
    (codeMat 281) (codeMat 482) (codeMat 143) false
    det281 det482 inv482
    (by rw [basis269]; decide +kernel)
    (by rw [basis269]; decide +kernel)

theorem space2359_lower : 16 ≤ frozenWangTable.L0 (spanCodes [81, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 269 space2359_orbit
  simpa only [lower269] using h

theorem space2360_orbit :
    frozenWangTable.OrbitImage 269 (spanCodes [80, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 269 [(80, 297), (9, 32), (4, 2), (3, 1)]
    (codeMat 345) (codeMat 226) (codeMat 141) false
    det345 det226 inv226
    (by rw [basis269]; decide +kernel)
    (by rw [basis269]; decide +kernel)

theorem space2360_lower : 16 ≤ frozenWangTable.L0 (spanCodes [80, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 269 space2360_orbit
  simpa only [lower269] using h

theorem space2361_orbit :
    frozenWangTable.OrbitImage 269 (spanCodes [81, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 269 [(81, 264), (8, 32), (5, 2), (2, 1)]
    (codeMat 337) (codeMat 354) (codeMat 142) false
    det337 det354 inv354
    (by rw [basis269]; decide +kernel)
    (by rw [basis269]; decide +kernel)

theorem space2361_lower : 16 ≤ frozenWangTable.L0 (spanCodes [81, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 269 space2361_orbit
  simpa only [lower269] using h

theorem space2362_orbit :
    frozenWangTable.OrbitImage 292 (spanCodes [64, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 292 [(64, 128), (16, 1), (10, 10), (4, 32)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    det266 det266 inv266
    (by rw [basis292]; decide +kernel)
    (by rw [basis292]; decide +kernel)

theorem space2362_lower : 16 ≤ frozenWangTable.L0 (spanCodes [64, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 292 space2362_orbit
  simpa only [lower292] using h

theorem space2363_orbit :
    frozenWangTable.OrbitImage 292 (spanCodes [64, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 292 [(64, 128), (17, 11), (10, 10), (5, 32)]
    (codeMat 267) (codeMat 314) (codeMat 271) false
    det267 det314 inv314
    (by rw [basis292]; decide +kernel)
    (by rw [basis292]; decide +kernel)

theorem space2363_lower : 16 ≤ frozenWangTable.L0 (spanCodes [64, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 292 space2363_orbit
  simpa only [lower292] using h

theorem space2364_orbit :
    frozenWangTable.OrbitImage 292 (spanCodes [65, 16, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 292 [(65, 128), (16, 1), (10, 10), (5, 32)]
    (codeMat 330) (codeMat 298) (codeMat 270) false
    det330 det298 inv298
    (by rw [basis292]; decide +kernel)
    (by rw [basis292]; decide +kernel)

theorem space2364_lower : 16 ≤ frozenWangTable.L0 (spanCodes [65, 16, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 292 space2364_orbit
  simpa only [lower292] using h

theorem space2365_orbit :
    frozenWangTable.OrbitImage 292 (spanCodes [65, 17, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 292 [(65, 128), (17, 11), (10, 10), (4, 32)]
    (codeMat 331) (codeMat 282) (codeMat 267) false
    det331 det282 inv282
    (by rw [basis292]; decide +kernel)
    (by rw [basis292]; decide +kernel)

theorem space2365_lower : 16 ≤ frozenWangTable.L0 (spanCodes [65, 17, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 292 space2365_orbit
  simpa only [lower292] using h

theorem space2366_orbit :
    frozenWangTable.OrbitImage 292 (spanCodes [66, 16, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 292 [(66, 138), (16, 1), (10, 10), (6, 32)]
    (codeMat 394) (codeMat 270) (codeMat 298) false
    det394 det270 inv270
    (by rw [basis292]; decide +kernel)
    (by rw [basis292]; decide +kernel)

theorem space2366_lower : 16 ≤ frozenWangTable.L0 (spanCodes [66, 16, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 292 space2366_orbit
  simpa only [lower292] using h

theorem space2367_orbit :
    frozenWangTable.OrbitImage 292 (spanCodes [66, 17, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 292 [(66, 138), (17, 11), (10, 10), (7, 32)]
    (codeMat 395) (codeMat 286) (codeMat 303) false
    det395 det286 inv286
    (by rw [basis292]; decide +kernel)
    (by rw [basis292]; decide +kernel)

theorem space2367_lower : 16 ≤ frozenWangTable.L0 (spanCodes [66, 17, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 292 space2367_orbit
  simpa only [lower292] using h


end QiushiMatmul.FrozenWang
