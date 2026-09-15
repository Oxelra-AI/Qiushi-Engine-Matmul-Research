import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space1792_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [354, 132, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(354, 305), (132, 338), (20, 336), (10, 304)]
    (codeMat 94) (codeMat 380) (codeMat 117) false
    det94 det380 inv380
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space1792_lower : 16 ≤ frozenWangTable.L0 (spanCodes [354, 132, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space1792_orbit
  simpa only [lower278] using h

theorem space1793_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [420, 66, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(420, 306), (66, 97), (20, 304), (10, 96)]
    (codeMat 142) (codeMat 417) (codeMat 177) false
    det142 det417 inv417
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space1793_lower : 16 ≤ frozenWangTable.L0 (spanCodes [420, 66, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space1793_orbit
  simpa only [lower278] using h

theorem space1794_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [323, 130, 39, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(323, 264), (130, 16), (39, 326), (20, 258), (10, 327)]
    (codeMat 107) (codeMat 377) (codeMat 369) false
    det107 det377 inv377
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space1794_lower : 16 ≤ frozenWangTable.L0 (spanCodes [323, 130, 39, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 150 space1794_orbit
  simpa only [lower150] using h

theorem space1795_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [262, 192, 32, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(262, 264), (192, 16), (32, 1), (20, 69), (10, 327)]
    (codeMat 98) (codeMat 207) (codeMat 370) false
    det98 det207 inv207
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space1795_lower : 16 ≤ frozenWangTable.L0 (spanCodes [262, 192, 32, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 150 space1795_orbit
  simpa only [lower150] using h

theorem space1796_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [258, 197, 32, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(258, 264), (197, 280), (32, 1), (20, 69), (10, 326)]
    (codeMat 106) (codeMat 206) (codeMat 498) false
    det106 det206 inv206
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space1796_lower : 16 ≤ frozenWangTable.L0 (spanCodes [258, 197, 32, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 150 space1796_orbit
  simpa only [lower150] using h

theorem space1797_orbit :
    frozenWangTable.OrbitImage 95 (spanCodes [32, 20, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 95 [(32, 2), (20, 20), (8, 1), (2, 32), (1, 8)]
    (codeMat 266) (codeMat 161) (codeMat 161) false
    det266 det161 inv161
    (by rw [basis95]; decide +kernel)
    (by rw [basis95]; decide +kernel)

theorem space1797_lower : 15 ≤ frozenWangTable.L0 (spanCodes [32, 20, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 95 space1797_orbit
  simpa only [lower95] using h

theorem space1798_orbit :
    frozenWangTable.OrbitImage 95 (spanCodes [32, 16, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 95 [(32, 1), (16, 2), (10, 20), (4, 8), (1, 32)]
    (codeMat 266) (codeMat 84) (codeMat 84) false
    det266 det84 inv84
    (by rw [basis95]; decide +kernel)
    (by rw [basis95]; decide +kernel)

theorem space1798_lower : 15 ≤ frozenWangTable.L0 (spanCodes [32, 16, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 95 space1798_orbit
  simpa only [lower95] using h

theorem space1799_orbit :
    frozenWangTable.OrbitImage 95 (spanCodes [32, 17, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 95 [(32, 2), (17, 62), (9, 63), (5, 40), (3, 8)]
    (codeMat 266) (codeMat 249) (codeMat 425) false
    det266 det249 inv249
    (by rw [basis95]; decide +kernel)
    (by rw [basis95]; decide +kernel)

theorem space1799_lower : 15 ≤ frozenWangTable.L0 (spanCodes [32, 17, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 95 space1799_orbit
  simpa only [lower95] using h

theorem space1800_orbit :
    frozenWangTable.OrbitImage 95 (spanCodes [33, 16, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 95 [(33, 20), (16, 1), (8, 2), (4, 32), (2, 8)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    det266 det266 inv266
    (by rw [basis95]; decide +kernel)
    (by rw [basis95]; decide +kernel)

theorem space1800_lower : 15 ≤ frozenWangTable.L0 (spanCodes [33, 16, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 95 space1800_orbit
  simpa only [lower95] using h

theorem space1801_orbit :
    frozenWangTable.OrbitImage 95 (spanCodes [34, 16, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 95 [(34, 20), (16, 2), (10, 21), (4, 32), (1, 40)]
    (codeMat 266) (codeMat 337) (codeMat 337) false
    det266 det337 inv337
    (by rw [basis95]; decide +kernel)
    (by rw [basis95]; decide +kernel)

theorem space1801_lower : 15 ≤ frozenWangTable.L0 (spanCodes [34, 16, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 95 space1801_orbit
  simpa only [lower95] using h

theorem space1802_orbit :
    frozenWangTable.OrbitImage 95 (spanCodes [36, 20, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 95 [(36, 54), (20, 52), (8, 1), (2, 32), (1, 8)]
    (codeMat 266) (codeMat 417) (codeMat 177) false
    det266 det417 inv417
    (by rw [basis95]; decide +kernel)
    (by rw [basis95]; decide +kernel)

theorem space1802_lower : 15 ≤ frozenWangTable.L0 (spanCodes [36, 20, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 95 space1802_orbit
  simpa only [lower95] using h

theorem space1803_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [68, 32, 20, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(68, 80), (32, 2), (20, 20), (8, 1), (2, 32), (1, 8)]
    (codeMat 266) (codeMat 161) (codeMat 161) false
    det266 det161 inv161
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space1803_lower : 15 ≤ frozenWangTable.L0 (spanCodes [68, 32, 20, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 31 space1803_orbit
  simpa only [lower31] using h

theorem space1804_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [129, 33, 16, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(129, 80), (33, 20), (16, 1), (8, 2), (4, 32), (2, 8)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    det266 det266 inv266
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space1804_lower : 15 ≤ frozenWangTable.L0 (spanCodes [129, 33, 16, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 31 space1804_orbit
  simpa only [lower31] using h

theorem space1805_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [128, 64, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(128, 1), (64, 8), (20, 132), (8, 32), (2, 2)]
    (codeMat 140) (codeMat 266) (codeMat 266) true
    det140 det266 inv266
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space1805_lower : 15 ≤ frozenWangTable.L0 (spanCodes [128, 64, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 103 space1805_orbit
  simpa only [lower103] using h

theorem space1806_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [129, 65, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(129, 11), (65, 8), (20, 166), (9, 32), (3, 2)]
    (codeMat 205) (codeMat 314) (codeMat 271) true
    det205 det314 inv314
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space1806_lower : 15 ≤ frozenWangTable.L0 (spanCodes [129, 65, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 103 space1806_orbit
  simpa only [lower103] using h

theorem space1807_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [128, 64, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(128, 9), (64, 8), (20, 166), (9, 32), (3, 2)]
    (codeMat 204) (codeMat 314) (codeMat 271) true
    det204 det314 inv314
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space1807_lower : 15 ≤ frozenWangTable.L0 (spanCodes [128, 64, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 103 space1807_orbit
  simpa only [lower103] using h

theorem space1808_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [128, 65, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(128, 3), (65, 8), (20, 132), (8, 32), (2, 2)]
    (codeMat 141) (codeMat 266) (codeMat 266) true
    det141 det266 inv266
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space1808_lower : 15 ≤ frozenWangTable.L0 (spanCodes [128, 65, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 103 space1808_orbit
  simpa only [lower103] using h

theorem space1809_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [132, 68, 20, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(132, 82), (68, 80), (20, 100), (8, 32), (2, 9), (1, 8)]
    (codeMat 161) (codeMat 282) (codeMat 267) true
    det161 det282 inv282
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space1809_lower : 15 ≤ frozenWangTable.L0 (spanCodes [132, 68, 20, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 31 space1809_orbit
  simpa only [lower31] using h

theorem space1810_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [132, 64, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(132, 133), (64, 40), (20, 132), (8, 32), (2, 2)]
    (codeMat 142) (codeMat 266) (codeMat 266) true
    det142 det266 inv266
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space1810_lower : 15 ≤ frozenWangTable.L0 (spanCodes [132, 64, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 103 space1810_orbit
  simpa only [lower103] using h

theorem space1811_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [133, 64, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(133, 173), (64, 40), (20, 166), (9, 32), (3, 2)]
    (codeMat 207) (codeMat 314) (codeMat 271) true
    det207 det314 inv314
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space1811_lower : 15 ≤ frozenWangTable.L0 (spanCodes [133, 64, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 103 space1811_orbit
  simpa only [lower103] using h

theorem space1812_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [132, 65, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(132, 175), (65, 40), (20, 166), (9, 32), (3, 2)]
    (codeMat 206) (codeMat 314) (codeMat 271) true
    det206 det314 inv314
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space1812_lower : 15 ≤ frozenWangTable.L0 (spanCodes [132, 65, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 103 space1812_orbit
  simpa only [lower103] using h

theorem space1813_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [132, 65, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(132, 135), (65, 40), (20, 132), (8, 32), (2, 2)]
    (codeMat 143) (codeMat 266) (codeMat 266) true
    det143 det266 inv266
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space1813_lower : 15 ≤ frozenWangTable.L0 (spanCodes [132, 65, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 103 space1813_orbit
  simpa only [lower103] using h

theorem space1814_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [128, 68, 20, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(128, 2), (68, 80), (20, 68), (8, 32), (2, 1), (1, 8)]
    (codeMat 161) (codeMat 266) (codeMat 266) true
    det161 det266 inv266
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space1814_lower : 15 ≤ frozenWangTable.L0 (spanCodes [128, 68, 20, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 31 space1814_orbit
  simpa only [lower31] using h

theorem space1815_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [193, 32, 17, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(193, 120), (32, 2), (17, 62), (9, 63), (5, 40), (3, 8)]
    (codeMat 266) (codeMat 249) (codeMat 425) false
    det266 det249 inv249
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space1815_lower : 15 ≤ frozenWangTable.L0 (spanCodes [193, 32, 17, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 31 space1815_orbit
  simpa only [lower31] using h

theorem space1816_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [260, 64, 38, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(260, 192), (64, 16), (38, 427), (20, 245), (10, 378)]
    (codeMat 358) (codeMat 174) (codeMat 359) false
    det358 det174 inv174
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space1816_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 64, 38, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space1816_orbit
  simpa only [lower220] using h

theorem space1817_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [258, 66, 38, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(258, 414), (66, 398), (38, 350), (20, 245), (10, 399)]
    (codeMat 486) (codeMat 181) (codeMat 423) false
    det486 det181 inv181
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space1817_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 66, 38, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space1817_orbit
  simpa only [lower220] using h

theorem space1818_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [256, 128, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(256, 8), (128, 1), (16, 2), (10, 132), (4, 32)]
    (codeMat 84) (codeMat 98) (codeMat 140) true
    det84 det98 inv98
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space1818_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 128, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 103 space1818_orbit
  simpa only [lower103] using h

theorem space1819_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [320, 192, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(320, 8), (192, 1), (17, 134), (10, 132), (5, 32)]
    (codeMat 92) (codeMat 482) (codeMat 143) true
    det92 det482 inv482
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space1819_lower : 15 ≤ frozenWangTable.L0 (spanCodes [320, 192, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 103 space1819_orbit
  simpa only [lower103] using h

theorem space1820_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [256, 130, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(256, 40), (130, 1), (16, 2), (10, 132), (4, 32)]
    (codeMat 85) (codeMat 98) (codeMat 140) true
    det85 det98 inv98
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space1820_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 130, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 103 space1820_orbit
  simpa only [lower103] using h

theorem space1821_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [320, 195, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(320, 40), (195, 1), (17, 134), (10, 132), (5, 32)]
    (codeMat 93) (codeMat 482) (codeMat 143) true
    det93 det482 inv482
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space1821_lower : 15 ≤ frozenWangTable.L0 (spanCodes [320, 195, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 103 space1821_orbit
  simpa only [lower103] using h

theorem space1822_orbit :
    frozenWangTable.OrbitImage 158 (spanCodes [258, 132, 38, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 158 [(258, 20), (132, 52), (38, 43), (20, 53), (10, 222)]
    (codeMat 358) (codeMat 110) (codeMat 444) true
    det358 det110 inv110
    (by rw [basis158]; decide +kernel)
    (by rw [basis158]; decide +kernel)

theorem space1822_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 132, 38, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 158 space1822_orbit
  simpa only [lower158] using h

theorem space1823_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [320, 192, 34, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(320, 8), (192, 9), (34, 134), (20, 132), (10, 166)]
    (codeMat 156) (codeMat 458) (codeMat 458) true
    det156 det458 inv458
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space1823_lower : 15 ≤ frozenWangTable.L0 (spanCodes [320, 192, 34, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 103 space1823_orbit
  simpa only [lower103] using h


end QiushiMatmul.FrozenWang
