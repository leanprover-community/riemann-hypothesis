module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
import Mathlib.SetTheory.Cardinal.Free
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.LatCount

theorem countable_subgroupClosure {G : Type*} [Group G] (s : Set G) (hs : s.Countable) :
    ((Subgroup.closure s : Subgroup G) : Set G).Countable := by
  open scoped Pointwise in
  have ht : (s ∪ s⁻¹).Countable := hs.union (by simpa using hs.image (·⁻¹))
  haveI : Countable ↥(s ∪ s⁻¹) := ht.to_subtype
  have h : ((Subgroup.closure s : Subgroup G) : Set G)
      = Set.range (FreeMonoid.lift ((↑) : ↥(s ∪ s⁻¹) → G)) := by
    have h1 : ((Subgroup.closure s : Subgroup G) : Set G)
        = ((Submonoid.closure (s ∪ s⁻¹) : Submonoid G) : Set G) := by
      rw [← Subgroup.closure_toSubmonoid]; rfl
    rw [h1, Submonoid.closure_eq_mrange]; rfl
  rw [h]
  exact Set.countable_range _

theorem countable_lat (K : Type) [Field K] [NumberField K] (n : ℕ) :
    Countable (PositivityTheory.Rg.Rs.An.lat K n) := by
  haveI : Countable K := GroundTheory.Global.countable_numberField K
  haveI : Countable (Matrix (Fin n) (Fin n) K) :=
    inferInstanceAs (Countable (Fin n → Fin n → K))
  haveI : Countable (GL (Fin n) K) := Units.val_injective.countable
  have h1 : (Set.range (AdelicGLn.diagonal K n)).Countable := Set.countable_range _
  have h2 : ((Subgroup.zpowers (PositivityTheory.Rg.Rs.An.tor K fun _ : Fin n => (1 : ℝ)) :
      Subgroup (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n)).Countable := by
    rw [Subgroup.coe_zpowers]
    exact Set.countable_range _
  have h3 := countable_subgroupClosure
    ((Set.range (AdelicGLn.diagonal K n)) ∪
      ((Subgroup.zpowers (PositivityTheory.Rg.Rs.An.tor K fun _ : Fin n => (1 : ℝ)) :
      Subgroup (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n))) (h1.union h2)
  have h4 : PositivityTheory.Rg.Rs.An.lat K n = Subgroup.closure
      ((Set.range (AdelicGLn.diagonal K n)) ∪
        ((Subgroup.zpowers (PositivityTheory.Rg.Rs.An.tor K fun _ : Fin n => (1 : ℝ)) :
        Subgroup (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n))) := by
    unfold PositivityTheory.Rg.Rs.An.lat
    rw [Subgroup.closure_union, Subgroup.closure_eq, ← MonoidHom.coe_range, Subgroup.closure_eq]
  rw [h4]
  exact h3.to_subtype

end GlobalTheory.CompanionTheory.LatCount
