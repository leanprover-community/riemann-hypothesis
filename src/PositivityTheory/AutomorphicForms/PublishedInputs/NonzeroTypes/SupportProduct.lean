module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CJDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CuspidalSupport2
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpCount
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpLat
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpLift
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpOrd
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpPiEta
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpPiSub
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpRes
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpSupp
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpTop
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpTwBasic
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpUniq
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ProductIrreducible2
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TensorVector

@[expose] public section

namespace UpperTheory.TNZ.Grp

theorem step_suppProd {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (G : Grp k n) : G.SupportOfProductProp :=
  step_spTop G UpperTheory.TNZ.step_spLat (step_spUniq G) (step_spCount G) (step_spLift G) (step_spTwBasic G) (step_spRes G)
    (step_spPiEta G) step_spOrd (step_spPiSub G) (step_spSupp G) UpperTheory.TNZ.step_cuspSupp UpperTheory.TNZ.step_prodIrr
    UpperTheory.TNZ.step_tensorVec

end UpperTheory.TNZ.Grp
