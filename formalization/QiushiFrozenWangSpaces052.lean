import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space1664_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [258, 128, 64, 32, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(258, 196), (128, 3), (64, 2), (32, 32), (18, 216), (10, 208), (4, 256), (1, 128)]
    (codeMat 84) (codeMat 282) (codeMat 267) false
    det84 det282 inv282
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1664_lower : 9 ≤ frozenWangTable.L0 (spanCodes [258, 128, 64, 32, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space1664_orbit
  simpa only [lower3] using h

theorem space1665_orbit :
    frozenWangTable.OrbitImage 452 (spanCodes [35, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 452 [(35, 35), (20, 10), (10, 61)]
    (codeMat 267) (codeMat 117) (codeMat 380) false
    det267 det117 inv117
    (by rw [basis452]; decide +kernel)
    (by rw [basis452]; decide +kernel)

theorem space1665_lower : 18 ≤ frozenWangTable.L0 (spanCodes [35, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 452 space1665_orbit
  simpa only [lower452] using h

theorem space1666_orbit :
    frozenWangTable.OrbitImage 452 (spanCodes [37, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 452 [(37, 41), (20, 10), (10, 20)]
    (codeMat 266) (codeMat 84) (codeMat 84) false
    det266 det84 inv84
    (by rw [basis452]; decide +kernel)
    (by rw [basis452]; decide +kernel)

theorem space1666_lower : 18 ≤ frozenWangTable.L0 (spanCodes [37, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 452 space1666_orbit
  simpa only [lower452] using h

theorem space1667_orbit :
    frozenWangTable.OrbitImage 453 (spanCodes [68, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 453 [(68, 68), (20, 20), (10, 10)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    det273 det273 inv273
    (by rw [basis453]; decide +kernel)
    (by rw [basis453]; decide +kernel)

theorem space1667_lower : 18 ≤ frozenWangTable.L0 (spanCodes [68, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 453 space1667_orbit
  simpa only [lower453] using h

theorem space1668_orbit :
    frozenWangTable.OrbitImage 453 (spanCodes [69, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 453 [(69, 68), (20, 30), (10, 10)]
    (codeMat 281) (codeMat 279) (codeMat 279) false
    det281 det279 inv279
    (by rw [basis453]; decide +kernel)
    (by rw [basis453]; decide +kernel)

theorem space1668_lower : 18 ≤ frozenWangTable.L0 (spanCodes [69, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 453 space1668_orbit
  simpa only [lower453] using h

theorem space1669_orbit :
    frozenWangTable.OrbitImage 453 (spanCodes [70, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 453 [(70, 78), (20, 20), (10, 10)]
    (codeMat 401) (codeMat 273) (codeMat 273) false
    det401 det273 inv273
    (by rw [basis453]; decide +kernel)
    (by rw [basis453]; decide +kernel)

theorem space1669_lower : 18 ≤ frozenWangTable.L0 (spanCodes [70, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 453 space1669_orbit
  simpa only [lower453] using h

theorem space1670_orbit :
    frozenWangTable.OrbitImage 453 (spanCodes [71, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 453 [(71, 78), (20, 30), (10, 10)]
    (codeMat 409) (codeMat 279) (codeMat 279) false
    det409 det279 inv279
    (by rw [basis453]; decide +kernel)
    (by rw [basis453]; decide +kernel)

theorem space1670_lower : 18 ≤ frozenWangTable.L0 (spanCodes [71, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 453 space1670_orbit
  simpa only [lower453] using h

theorem space1671_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [96, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(96, 96), (20, 20), (10, 10)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    det273 det273 inv273
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space1671_lower : 18 ≤ frozenWangTable.L0 (spanCodes [96, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space1671_orbit
  simpa only [lower454] using h

theorem space1672_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [97, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(97, 96), (20, 20), (10, 10)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    det337 det273 inv273
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space1672_lower : 18 ≤ frozenWangTable.L0 (spanCodes [97, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space1672_orbit
  simpa only [lower454] using h

theorem space1673_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [98, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(98, 106), (20, 20), (10, 10)]
    (codeMat 401) (codeMat 273) (codeMat 273) false
    det401 det273 inv273
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space1673_lower : 18 ≤ frozenWangTable.L0 (spanCodes [98, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space1673_orbit
  simpa only [lower454] using h

theorem space1674_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [99, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(99, 106), (20, 20), (10, 10)]
    (codeMat 465) (codeMat 273) (codeMat 273) false
    det465 det273 inv273
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space1674_lower : 18 ≤ frozenWangTable.L0 (spanCodes [99, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space1674_orbit
  simpa only [lower454] using h

theorem space1675_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [100, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(100, 96), (20, 30), (10, 10)]
    (codeMat 473) (codeMat 279) (codeMat 279) false
    det473 det279 inv279
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space1675_lower : 18 ≤ frozenWangTable.L0 (spanCodes [100, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space1675_orbit
  simpa only [lower454] using h

theorem space1676_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [101, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(101, 96), (20, 30), (10, 10)]
    (codeMat 409) (codeMat 279) (codeMat 279) false
    det409 det279 inv279
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space1676_lower : 18 ≤ frozenWangTable.L0 (spanCodes [101, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space1676_orbit
  simpa only [lower454] using h

theorem space1677_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [102, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(102, 106), (20, 30), (10, 10)]
    (codeMat 345) (codeMat 279) (codeMat 279) false
    det345 det279 inv279
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space1677_lower : 18 ≤ frozenWangTable.L0 (spanCodes [102, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space1677_orbit
  simpa only [lower454] using h

theorem space1678_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [103, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(103, 106), (20, 30), (10, 10)]
    (codeMat 281) (codeMat 279) (codeMat 279) false
    det281 det279 inv279
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space1678_lower : 18 ≤ frozenWangTable.L0 (spanCodes [103, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space1678_orbit
  simpa only [lower454] using h

theorem space1679_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [129, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(129, 129), (20, 20), (10, 10)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    det273 det273 inv273
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space1679_lower : 18 ≤ frozenWangTable.L0 (spanCodes [129, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space1679_orbit
  simpa only [lower455] using h

theorem space1680_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [131, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(131, 129), (20, 20), (10, 10)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    det337 det273 inv273
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space1680_lower : 18 ≤ frozenWangTable.L0 (spanCodes [131, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space1680_orbit
  simpa only [lower455] using h

theorem space1681_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [133, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(133, 149), (20, 20), (10, 10)]
    (codeMat 401) (codeMat 273) (codeMat 273) false
    det401 det273 inv273
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space1681_lower : 18 ≤ frozenWangTable.L0 (spanCodes [133, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space1681_orbit
  simpa only [lower455] using h

theorem space1682_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [135, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(135, 149), (20, 20), (10, 10)]
    (codeMat 465) (codeMat 273) (codeMat 273) false
    det465 det273 inv273
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space1682_lower : 18 ≤ frozenWangTable.L0 (spanCodes [135, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space1682_orbit
  simpa only [lower455] using h

theorem space1683_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [160, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(160, 129), (20, 10), (10, 20)]
    (codeMat 266) (codeMat 84) (codeMat 84) false
    det266 det84 inv84
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space1683_lower : 18 ≤ frozenWangTable.L0 (spanCodes [160, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space1683_orbit
  simpa only [lower455] using h

theorem space1684_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [161, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(161, 161), (20, 10), (10, 20)]
    (codeMat 266) (codeMat 84) (codeMat 84) false
    det266 det84 inv84
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space1684_lower : 18 ≤ frozenWangTable.L0 (spanCodes [161, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space1684_orbit
  simpa only [lower456] using h

theorem space1685_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [162, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(162, 129), (20, 10), (10, 20)]
    (codeMat 330) (codeMat 84) (codeMat 84) false
    det330 det84 inv84
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space1685_lower : 18 ≤ frozenWangTable.L0 (spanCodes [162, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space1685_orbit
  simpa only [lower455] using h

theorem space1686_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [163, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(163, 161), (20, 10), (10, 20)]
    (codeMat 330) (codeMat 84) (codeMat 84) false
    det330 det84 inv84
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space1686_lower : 18 ≤ frozenWangTable.L0 (spanCodes [163, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space1686_orbit
  simpa only [lower456] using h

theorem space1687_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [164, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(164, 139), (20, 10), (10, 20)]
    (codeMat 394) (codeMat 84) (codeMat 84) false
    det394 det84 inv84
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space1687_lower : 18 ≤ frozenWangTable.L0 (spanCodes [164, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space1687_orbit
  simpa only [lower455] using h

theorem space1688_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [165, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(165, 171), (20, 10), (10, 20)]
    (codeMat 394) (codeMat 84) (codeMat 84) false
    det394 det84 inv84
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space1688_lower : 18 ≤ frozenWangTable.L0 (spanCodes [165, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space1688_orbit
  simpa only [lower456] using h

theorem space1689_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [166, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(166, 139), (20, 10), (10, 20)]
    (codeMat 458) (codeMat 84) (codeMat 84) false
    det458 det84 inv84
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space1689_lower : 18 ≤ frozenWangTable.L0 (spanCodes [166, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space1689_orbit
  simpa only [lower455] using h

theorem space1690_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [167, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(167, 171), (20, 10), (10, 20)]
    (codeMat 458) (codeMat 84) (codeMat 84) false
    det458 det84 inv84
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space1690_lower : 18 ≤ frozenWangTable.L0 (spanCodes [167, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space1690_orbit
  simpa only [lower456] using h

theorem space1691_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [193, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(193, 129), (20, 30), (10, 10)]
    (codeMat 281) (codeMat 279) (codeMat 279) false
    det281 det279 inv279
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space1691_lower : 18 ≤ frozenWangTable.L0 (spanCodes [193, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space1691_orbit
  simpa only [lower455] using h

theorem space1692_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [194, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(194, 129), (20, 30), (10, 10)]
    (codeMat 345) (codeMat 279) (codeMat 279) false
    det345 det279 inv279
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space1692_lower : 18 ≤ frozenWangTable.L0 (spanCodes [194, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space1692_orbit
  simpa only [lower455] using h

theorem space1693_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [196, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(196, 149), (20, 30), (10, 10)]
    (codeMat 473) (codeMat 279) (codeMat 279) false
    det473 det279 inv279
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space1693_lower : 18 ≤ frozenWangTable.L0 (spanCodes [196, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space1693_orbit
  simpa only [lower455] using h

theorem space1694_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [199, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(199, 149), (20, 30), (10, 10)]
    (codeMat 409) (codeMat 279) (codeMat 279) false
    det409 det279 inv279
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space1694_lower : 18 ≤ frozenWangTable.L0 (spanCodes [199, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space1694_orbit
  simpa only [lower455] using h

theorem space1695_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [224, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(224, 191), (20, 30), (10, 20)]
    (codeMat 395) (codeMat 468) (codeMat 87) false
    det395 det468 inv468
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space1695_lower : 18 ≤ frozenWangTable.L0 (spanCodes [224, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space1695_orbit
  simpa only [lower456] using h


end QiushiMatmul.FrozenWang
