import QiushiFrozenRankCoverMixed
import QiushiCertifiedTransport
import QiushiPlane267GenBindings00
import QiushiWcOrbit165Dispatch
import QiushiPlane298GenBindings00
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit236Dispatch
import QiushiOrbit35FP
import QiushiPlane152GenBindings00
import QiushiOrbit10FP
import QiushiFrozenWangData

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

open BigOperators

namespace QiushiMatmul.FrozenRank

def sources357 : Fin 13 → List Nat := ![
  [298,96,18,6,1],
  [288,96,20,10,1],
  [292,96,20,14,1],
  [298,138,96,20,1],
  [298,142,96,20,1],
  [298,164,96,20,1],
  [298,168,96,20,1],
  [290,96,16,8,4,1],
  [262,68,36,20,8,1],
  [268,140,70,38,20,1],
  [260,136,78,46,20,1],
  [264,128,64,32,20,2,1],
  [256,132,72,40,20,2,1]]

def lower357 : Fin 13 → Nat := ![15,15,15,16,16,16,16,15,15,15,15,12,12]

theorem sources357_rank (i : Fin 13) :
    QuotientRankAtLeast (spanCodes (sources357 i)) (lower357 i) := by
  fin_cases i
  · exact quotientRankAtLeast_of_code_transport
      [408,84,32,2,1]
      [(298,443),(96,118),(18,32),(6,2),(1,1)]
      (codeMat 281) (codeMat 417) (codeMat 177) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      plane267GenBound0009
  · exact step109_orbit165_lb15_wc
  · exact quotientRankAtLeast_of_code_transport
      [384,84,32,10,1]
      [(292,511),(96,126),(20,42),(14,11),(1,1)]
      (codeMat 345) (codeMat 423) (codeMat 181) false
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      plane298GenBound0004
  · exact quotientRankAtLeast_of_code_transport
      [278,132,96,10,1]
      [(298,143),(138,238),(96,96),(20,381),(1,504)]
      (codeMat 412) (codeMat 234) (codeMat 461) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      step109_orbit214_lb16_wc
  · exact quotientRankAtLeast_of_code_transport
      [278,132,96,10,1]
      [(298,239),(142,107),(96,96),(20,133),(1,504)]
      (codeMat 286) (codeMat 458) (codeMat 458) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      step109_orbit214_lb16_wc
  · exact quotientRankAtLeast_of_code_transport
      [262,136,96,20,1]
      [(298,358),(164,371),(96,507),(20,399),(1,1)]
      (codeMat 425) (codeMat 419) (codeMat 183) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      step109_orbit236_lb16_wc
  · exact quotientRankAtLeast_of_code_transport
      [262,136,96,20,1]
      [(298,157),(168,252),(96,507),(20,398),(1,1)]
      (codeMat 313) (codeMat 423) (codeMat 181) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      step109_orbit236_lb16_wc
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,20,96,128]
      [(290,118),(96,22),(16,128),(8,2),(4,9),(1,1)]
      (codeMat 273) (codeMat 165) (codeMat 163) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit35_lb15
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,20,96,128]
      [(262,224),(68,28),(36,8),(20,136),(8,2),(1,3)]
      (codeMat 275) (codeMat 177) (codeMat 417) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit35_lb15
  · exact quotientRankAtLeast_of_code_transport
      [256,164,96,16,10,1]
      [(268,96),(140,123),(70,10),(38,378),(20,469),(1,16)]
      (codeMat 461) (codeMat 426) (codeMat 335) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      plane152GenBound0001
  · exact quotientRankAtLeast_of_code_transport
      [256,164,96,16,10,1]
      [(260,256),(136,430),(78,26),(46,362),(20,453),(1,16)]
      (codeMat 335) (codeMat 394) (codeMat 330) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      plane152GenBound0001
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,16,68,160,256]
      [(264,160),(128,2),(64,16),(32,256),(20,68),(2,1),(1,8)]
      (codeMat 161) (codeMat 266) (codeMat 266) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit10_lb12
  · exact quotientRankAtLeast_of_code_transport
      [1,2,8,16,68,160,256]
      [(256,432),(132,78),(72,16),(40,256),(20,76),(2,1),(1,8)]
      (codeMat 177) (codeMat 298) (codeMat 270) true
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      orbit10_lb12

theorem sources357_contain : ∀ i g, g ∈ [298,96,20,1] →
    spanContainsCode (sources357 i) g = true := by
  decide +kernel

theorem sources357_cover : ∀ c : Fin 512,
    ∃ i : Fin 13, spanContainsCode (sources357 i) c.val = true := by
  decide +kernel

theorem capacity357 (r : Nat) (hr : r < 17) (hlower : ∀ i, lower357 i ≤ r) :
    (∑ i : Fin 13, (r - lower357 i)) < r := by
  have h16 : 16 ≤ r := hlower 3
  have heq : r = 16 := by omega
  subst r
  decide +kernel

theorem span357_lb17 : QuotientRankAtLeast (spanCodes [298,96,20,1]) 17 :=
  quotientRankAtLeast_of_mixed_code_cover _ sources357 lower357
    sources357_rank sources357_contain sources357_cover capacity357

theorem rep357 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 357))
      (frozenWangTable.lower 357) := by
  exact span357_lb17

end QiushiMatmul.FrozenRank
