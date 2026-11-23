module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.PoincareInHH.Cut

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem poincare_well_defined (hK : X.LevelSubgroupCharacter) (hS : KsetSplit X u) (hN : UnipotentConjugateInLevel X u) : PhWellDef X u hK :=
  phWellDef_of_steps X u hK hS hN

theorem poincare_properties (hK : X.LevelSubgroupCharacter) (hR : FoldReadyX X) (hS : KsetSplit X u) (hN : UnipotentConjugateInLevel X u)
    (hL : RatLevi X u) (hP : PsiProd X u) : PhProps X u hK :=
  phProps_of_steps X u hK (Formalism.L2.SG.Closed.level_subgroup_properties X) hR hS hN hL hP

theorem foldReadyX_holds : FoldReadyX X := Formalism.L2.SG.Pf.foldReady_holds X.B.I

theorem sratFund_holds : SratFund X u := by
  obtain ⟨Fs, -, h⟩ := Formalism.L2.SG.Pf.exists_fund_srat_holds X u
  exact ⟨Fs, h _⟩

theorem phProps_closed (hK : X.LevelSubgroupCharacter) (hS : KsetSplit X u) (hN : UnipotentConjugateInLevel X u) (hL : RatLevi X u)
    (hP : PsiProd X u) : PhProps X u hK :=
  poincare_properties X u hK (foldReadyX_holds X) hS hN hL hP

end Formalism.L2.SG.PoincareInHH.Cut
