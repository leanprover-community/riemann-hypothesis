module

public import Development.EtaleCohomology.KummerTheory.InjSlice
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Comma.LocallySmall
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def ForgetInj : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) [Injective F] (S : Scheme.{0}),
  ∃ h : Presheaf.IsSheaf (Scheme.etaleTopology.over S) ((Over.forget S).op ⋙ F.obj),
    Injective (⟨_, h⟩ : Sheaf (Scheme.etaleTopology.over S) (ModuleCat.{1} (ULift.{1} R)))

theorem pushPullback_inj {R : Type} [CommRing R] {X S : Scheme.{0}} (p : X ⟶ S)
    (G : Sheaf (Scheme.etaleTopology.over X) (ModuleCat.{1} (ULift.{1} R))) [Injective G] :
    Injective (((Over.pullback p).sheafPushforwardContinuous (ModuleCat.{1} (ULift.{1} R))
      (Scheme.etaleTopology.over S) (Scheme.etaleTopology.over X)).obj G) := by
  have adj := (Over.mapPullbackAdj p).sheafPushforwardContinuous (E := ModuleCat.{1} (ULift.{1} R))
    (Scheme.etaleTopology.over X) (Scheme.etaleTopology.over S)
  have : ((Over.map p).sheafPushforwardContinuous (ModuleCat.{1} (ULift.{1} R))
      (Scheme.etaleTopology.over X) (Scheme.etaleTopology.over S)).PreservesMonomorphisms := inferInstance
  exact Injective.injective_of_adjoint adj G

theorem InjSlice_of (hF : ForgetInj) : InjSlice := by
  intro R _ F _ X S p
  obtain ⟨hX, iX⟩ := hF R F X
  refine ⟨?_, hF R F S⟩
  let G : Sheaf (Scheme.etaleTopology.over X) (ModuleCat.{1} (ULift.{1} R)) := ⟨_, hX⟩
  exact ⟨(((Over.pullback p).sheafPushforwardContinuous (ModuleCat.{1} (ULift.{1} R))
      (Scheme.etaleTopology.over S) (Scheme.etaleTopology.over X)).obj G).2, pushPullback_inj p G⟩

end LateralTheory.KummerTheory
