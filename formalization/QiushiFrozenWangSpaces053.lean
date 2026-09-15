import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space1696_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [225, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(225, 159), (20, 30), (10, 20)]
    (codeMat 395) (codeMat 468) (codeMat 87) false
    det395 det468 inv468
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space1696_lower : 18 ≤ frozenWangTable.L0 (spanCodes [225, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space1696_orbit
  simpa only [lower455] using h

theorem space1697_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [226, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(226, 159), (20, 30), (10, 20)]
    (codeMat 459) (codeMat 468) (codeMat 87) false
    det459 det468 inv468
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space1697_lower : 18 ≤ frozenWangTable.L0 (spanCodes [226, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space1697_orbit
  simpa only [lower455] using h

theorem space1698_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [227, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(227, 191), (20, 30), (10, 20)]
    (codeMat 459) (codeMat 468) (codeMat 87) false
    det459 det468 inv468
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space1698_lower : 18 ≤ frozenWangTable.L0 (spanCodes [227, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space1698_orbit
  simpa only [lower456] using h

theorem space1699_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [228, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(228, 149), (20, 30), (10, 20)]
    (codeMat 331) (codeMat 468) (codeMat 87) false
    det331 det468 inv468
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space1699_lower : 18 ≤ frozenWangTable.L0 (spanCodes [228, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space1699_orbit
  simpa only [lower455] using h

theorem space1700_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [229, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(229, 181), (20, 30), (10, 20)]
    (codeMat 331) (codeMat 468) (codeMat 87) false
    det331 det468 inv468
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space1700_lower : 18 ≤ frozenWangTable.L0 (spanCodes [229, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space1700_orbit
  simpa only [lower456] using h

theorem space1701_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [230, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(230, 181), (20, 30), (10, 20)]
    (codeMat 267) (codeMat 468) (codeMat 87) false
    det267 det468 inv468
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space1701_lower : 18 ≤ frozenWangTable.L0 (spanCodes [230, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space1701_orbit
  simpa only [lower456] using h

theorem space1702_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [231, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(231, 149), (20, 30), (10, 20)]
    (codeMat 267) (codeMat 468) (codeMat 87) false
    det267 det468 inv468
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space1702_lower : 18 ≤ frozenWangTable.L0 (spanCodes [231, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space1702_orbit
  simpa only [lower455] using h

theorem space1703_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [257, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(257, 96), (20, 10), (10, 20)]
    (codeMat 266) (codeMat 84) (codeMat 84) false
    det266 det84 inv84
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space1703_lower : 18 ≤ frozenWangTable.L0 (spanCodes [257, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space1703_orbit
  simpa only [lower454] using h

theorem space1704_orbit :
    frozenWangTable.OrbitImage 453 (spanCodes [258, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 453 [(258, 80), (20, 10), (10, 20)]
    (codeMat 266) (codeMat 84) (codeMat 84) false
    det266 det84 inv84
    (by rw [basis453]; decide +kernel)
    (by rw [basis453]; decide +kernel)

theorem space1704_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 453 space1704_orbit
  simpa only [lower453] using h

theorem space1705_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [259, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(259, 126), (20, 10), (10, 30)]
    (codeMat 474) (codeMat 87) (codeMat 468) false
    det474 det87 inv87
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space1705_lower : 18 ≤ frozenWangTable.L0 (spanCodes [259, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space1705_orbit
  simpa only [lower454] using h

theorem space1706_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [261, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(261, 96), (20, 10), (10, 20)]
    (codeMat 330) (codeMat 84) (codeMat 84) false
    det330 det84 inv84
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space1706_lower : 18 ≤ frozenWangTable.L0 (spanCodes [261, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space1706_orbit
  simpa only [lower454] using h

theorem space1707_orbit :
    frozenWangTable.OrbitImage 453 (spanCodes [262, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 453 [(262, 80), (20, 10), (10, 20)]
    (codeMat 330) (codeMat 84) (codeMat 84) false
    det330 det84 inv84
    (by rw [basis453]; decide +kernel)
    (by rw [basis453]; decide +kernel)

theorem space1707_lower : 18 ≤ frozenWangTable.L0 (spanCodes [262, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 453 space1707_orbit
  simpa only [lower453] using h

theorem space1708_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [263, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(263, 126), (20, 10), (10, 30)]
    (codeMat 410) (codeMat 87) (codeMat 468) false
    det410 det87 inv87
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space1708_lower : 18 ≤ frozenWangTable.L0 (spanCodes [263, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space1708_orbit
  simpa only [lower454] using h

theorem space1709_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [289, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(289, 96), (20, 10), (10, 20)]
    (codeMat 394) (codeMat 84) (codeMat 84) false
    det394 det84 inv84
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space1709_lower : 18 ≤ frozenWangTable.L0 (spanCodes [289, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space1709_orbit
  simpa only [lower454] using h

theorem space1710_orbit :
    frozenWangTable.OrbitImage 453 (spanCodes [290, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 453 [(290, 90), (20, 10), (10, 30)]
    (codeMat 282) (codeMat 87) (codeMat 468) false
    det282 det87 inv87
    (by rw [basis453]; decide +kernel)
    (by rw [basis453]; decide +kernel)

theorem space1710_lower : 18 ≤ frozenWangTable.L0 (spanCodes [290, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 453 space1710_orbit
  simpa only [lower453] using h

theorem space1711_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [291, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(291, 126), (20, 10), (10, 30)]
    (codeMat 346) (codeMat 87) (codeMat 468) false
    det346 det87 inv87
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space1711_lower : 18 ≤ frozenWangTable.L0 (spanCodes [291, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space1711_orbit
  simpa only [lower454] using h

theorem space1712_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [293, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(293, 96), (20, 10), (10, 20)]
    (codeMat 458) (codeMat 84) (codeMat 84) false
    det458 det84 inv84
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space1712_lower : 18 ≤ frozenWangTable.L0 (spanCodes [293, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space1712_orbit
  simpa only [lower454] using h

theorem space1713_orbit :
    frozenWangTable.OrbitImage 453 (spanCodes [294, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 453 [(294, 90), (20, 10), (10, 30)]
    (codeMat 346) (codeMat 87) (codeMat 468) false
    det346 det87 inv87
    (by rw [basis453]; decide +kernel)
    (by rw [basis453]; decide +kernel)

theorem space1713_lower : 18 ≤ frozenWangTable.L0 (spanCodes [294, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 453 space1713_orbit
  simpa only [lower453] using h

theorem space1714_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [295, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(295, 126), (20, 10), (10, 30)]
    (codeMat 282) (codeMat 87) (codeMat 468) false
    det282 det87 inv87
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space1714_lower : 18 ≤ frozenWangTable.L0 (spanCodes [295, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space1714_orbit
  simpa only [lower454] using h

theorem space1715_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [321, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(321, 96), (20, 30), (10, 20)]
    (codeMat 267) (codeMat 468) (codeMat 87) false
    det267 det468 inv468
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space1715_lower : 18 ≤ frozenWangTable.L0 (spanCodes [321, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space1715_orbit
  simpa only [lower454] using h

theorem space1716_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [322, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(322, 126), (20, 20), (10, 30)]
    (codeMat 403) (codeMat 465) (codeMat 465) false
    det403 det465 inv465
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space1716_lower : 18 ≤ frozenWangTable.L0 (spanCodes [322, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space1716_orbit
  simpa only [lower454] using h

theorem space1717_orbit :
    frozenWangTable.OrbitImage 453 (spanCodes [323, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 453 [(323, 80), (20, 30), (10, 20)]
    (codeMat 267) (codeMat 468) (codeMat 87) false
    det267 det468 inv468
    (by rw [basis453]; decide +kernel)
    (by rw [basis453]; decide +kernel)

theorem space1717_lower : 18 ≤ frozenWangTable.L0 (spanCodes [323, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 453 space1717_orbit
  simpa only [lower453] using h

theorem space1718_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [324, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(324, 96), (20, 30), (10, 20)]
    (codeMat 331) (codeMat 468) (codeMat 87) false
    det331 det468 inv468
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space1718_lower : 18 ≤ frozenWangTable.L0 (spanCodes [324, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space1718_orbit
  simpa only [lower454] using h

theorem space1719_orbit :
    frozenWangTable.OrbitImage 453 (spanCodes [326, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 453 [(326, 80), (20, 30), (10, 20)]
    (codeMat 331) (codeMat 468) (codeMat 87) false
    det331 det468 inv468
    (by rw [basis453]; decide +kernel)
    (by rw [basis453]; decide +kernel)

theorem space1719_lower : 18 ≤ frozenWangTable.L0 (spanCodes [326, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 453 space1719_orbit
  simpa only [lower453] using h

theorem space1720_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [327, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(327, 126), (20, 20), (10, 30)]
    (codeMat 467) (codeMat 465) (codeMat 465) false
    det467 det465 inv465
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space1720_lower : 18 ≤ frozenWangTable.L0 (spanCodes [327, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space1720_orbit
  simpa only [lower454] using h

theorem space1721_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [352, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(352, 96), (20, 20), (10, 30)]
    (codeMat 275) (codeMat 465) (codeMat 465) false
    det275 det465 inv465
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space1721_lower : 18 ≤ frozenWangTable.L0 (spanCodes [352, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space1721_orbit
  simpa only [lower454] using h

theorem space1722_orbit :
    frozenWangTable.OrbitImage 453 (spanCodes [353, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 453 [(353, 68), (20, 20), (10, 30)]
    (codeMat 339) (codeMat 465) (codeMat 465) false
    det339 det465 inv465
    (by rw [basis453]; decide +kernel)
    (by rw [basis453]; decide +kernel)

theorem space1722_lower : 18 ≤ frozenWangTable.L0 (spanCodes [353, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 453 space1722_orbit
  simpa only [lower453] using h

theorem space1723_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [355, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(355, 116), (20, 30), (10, 20)]
    (codeMat 395) (codeMat 468) (codeMat 87) false
    det395 det468 inv468
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space1723_lower : 18 ≤ frozenWangTable.L0 (spanCodes [355, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space1723_orbit
  simpa only [lower454] using h

theorem space1724_orbit :
    frozenWangTable.OrbitImage 453 (spanCodes [356, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 453 [(356, 68), (20, 20), (10, 30)]
    (codeMat 275) (codeMat 465) (codeMat 465) false
    det275 det465 inv465
    (by rw [basis453]; decide +kernel)
    (by rw [basis453]; decide +kernel)

theorem space1724_lower : 18 ≤ frozenWangTable.L0 (spanCodes [356, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 453 space1724_orbit
  simpa only [lower453] using h

theorem space1725_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [357, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(357, 96), (20, 20), (10, 30)]
    (codeMat 339) (codeMat 465) (codeMat 465) false
    det339 det465 inv465
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space1725_lower : 18 ≤ frozenWangTable.L0 (spanCodes [357, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space1725_orbit
  simpa only [lower454] using h

theorem space1726_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [358, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(358, 116), (20, 30), (10, 20)]
    (codeMat 459) (codeMat 468) (codeMat 87) false
    det459 det468 inv468
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space1726_lower : 18 ≤ frozenWangTable.L0 (spanCodes [358, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space1726_orbit
  simpa only [lower454] using h

theorem space1727_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [385, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(385, 191), (20, 20), (10, 30)]
    (codeMat 339) (codeMat 465) (codeMat 465) false
    det339 det465 inv465
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space1727_lower : 18 ≤ frozenWangTable.L0 (spanCodes [385, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space1727_orbit
  simpa only [lower456] using h


end QiushiMatmul.FrozenWang
