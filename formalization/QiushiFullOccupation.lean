import QiushiFrozenWangBindings
import QiushiFullOccupationSystemBridge
import QiushiPlane484StrictFinal
import QiushiPlane484GenTree
import QiushiPlane485StrictFinal
import QiushiPlane485GenTree
import QiushiPlane486StrictFinal
import QiushiPlane486GenTree
import QiushiPlane487StrictFinal
import QiushiPlane487GenTree
import QiushiPlane488StrictFinal
import QiushiPlane488GenTree
import QiushiPlane489StrictFinal
import QiushiPlane489GenTree
import QiushiPlane490StrictFinal
import QiushiPlane490GenTree
import QiushiPlane491StrictFinal
import QiushiPlane491GenTree

/-! The eight full integer occupation systems have no model.
The table is the fixed mathematical orbit expansion, not an opaque pickle.
All selected numeric and strict-subspace obligations are discharged below.
These statements quantify over arbitrary nonnegative integer weights;
tensor realizability and distinct support are not assumed. -/

namespace QiushiMatmul.FrozenOccupation
open OccupationSystemBridge

theorem plane484_no_model (weight : Direction plane484GenConfig.W → Int)
    (h : FullOccupation plane484GenConfig frozenWangTable.L0 weight) : False :=
  full_occupation_no_model plane484GenConfig plane484GenBool plane484GenNoModel
    frozenWangTable.L0
    (FullOccupationBinding.of_paired plane484GenConfig frozenWangTable.L0
      plane484SourceStrict plane484DeadStrict
      FrozenWang.plane484_source FrozenWang.plane484_dead) weight h

theorem plane485_no_model (weight : Direction plane485GenConfig.W → Int)
    (h : FullOccupation plane485GenConfig frozenWangTable.L0 weight) : False :=
  full_occupation_no_model plane485GenConfig plane485GenBool plane485GenNoModel
    frozenWangTable.L0
    (FullOccupationBinding.of_paired plane485GenConfig frozenWangTable.L0
      plane485SourceStrict plane485DeadStrict
      FrozenWang.plane485_source FrozenWang.plane485_dead) weight h

theorem plane486_no_model (weight : Direction plane486GenConfig.W → Int)
    (h : FullOccupation plane486GenConfig frozenWangTable.L0 weight) : False :=
  full_occupation_no_model plane486GenConfig plane486GenBool plane486GenNoModel
    frozenWangTable.L0
    (FullOccupationBinding.of_paired plane486GenConfig frozenWangTable.L0
      plane486SourceStrict plane486DeadStrict
      FrozenWang.plane486_source FrozenWang.plane486_dead) weight h

theorem plane487_no_model (weight : Direction plane487GenConfig.W → Int)
    (h : FullOccupation plane487GenConfig frozenWangTable.L0 weight) : False :=
  full_occupation_no_model plane487GenConfig plane487GenBool plane487GenNoModel
    frozenWangTable.L0
    (FullOccupationBinding.of_paired plane487GenConfig frozenWangTable.L0
      plane487SourceStrict plane487DeadStrict
      FrozenWang.plane487_source FrozenWang.plane487_dead) weight h

theorem plane488_no_model (weight : Direction plane488GenConfig.W → Int)
    (h : FullOccupation plane488GenConfig frozenWangTable.L0 weight) : False :=
  full_occupation_no_model plane488GenConfig plane488GenBool plane488GenNoModel
    frozenWangTable.L0
    (FullOccupationBinding.of_paired plane488GenConfig frozenWangTable.L0
      plane488SourceStrict plane488DeadStrict
      FrozenWang.plane488_source FrozenWang.plane488_dead) weight h

theorem plane489_no_model (weight : Direction plane489GenConfig.W → Int)
    (h : FullOccupation plane489GenConfig frozenWangTable.L0 weight) : False :=
  full_occupation_no_model plane489GenConfig plane489GenBool plane489GenNoModel
    frozenWangTable.L0
    (FullOccupationBinding.of_paired plane489GenConfig frozenWangTable.L0
      plane489SourceStrict plane489DeadStrict
      FrozenWang.plane489_source FrozenWang.plane489_dead) weight h

theorem plane490_no_model (weight : Direction plane490GenConfig.W → Int)
    (h : FullOccupation plane490GenConfig frozenWangTable.L0 weight) : False :=
  full_occupation_no_model plane490GenConfig plane490GenBool plane490GenNoModel
    frozenWangTable.L0
    (FullOccupationBinding.of_paired plane490GenConfig frozenWangTable.L0
      plane490SourceStrict plane490DeadStrict
      FrozenWang.plane490_source FrozenWang.plane490_dead) weight h

theorem plane491_no_model (weight : Direction plane491GenConfig.W → Int)
    (h : FullOccupation plane491GenConfig frozenWangTable.L0 weight) : False :=
  full_occupation_no_model plane491GenConfig plane491GenBool plane491GenNoModel
    frozenWangTable.L0
    (FullOccupationBinding.of_paired plane491GenConfig frozenWangTable.L0
      plane491SourceStrict plane491DeadStrict
      FrozenWang.plane491_source FrozenWang.plane491_dead) weight h

end QiushiMatmul.FrozenOccupation
