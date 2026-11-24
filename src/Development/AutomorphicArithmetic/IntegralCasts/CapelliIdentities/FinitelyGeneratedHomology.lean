module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsCompactUnitaryPointsAtPlaceFstMemCompact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

theorem UpperTheory.Reformulated.B.FinitelyGeneratedHomology.omHT_fg :
    ∀ {A K : Type} [inst : CommRing A] [inst_1 : Field K] [inst_2 : Algebra A K] {E : Type} [inst_3 : Field E]
      [inst_4 : NumberField E] {c : E ≃+* E} {p R N : ℕ} {Ω : Type} [inst_5 : AddCommGroup Ω] [inst_6 : _root_.Module K Ω]
      [inst_7 : _root_.Module A Ω] [inst_8 : IsScalarTower A K Ω] (D : GlobalTheory.CompanionTheory.Ar.HT.HTChart A K c p R N Ω) (σ : E →+* K),
      (D.omHT σ).FG := by
  intro A K _ _ _ E _ _ c p R N Ω _ _ _ _ D σ
  have hZ : (LinearMap.range D.h.toIntLinearMap).FG := Submodule.fg_range _
  have hA : (Submodule.span A (Set.range D.h)).FG := by
    obtain ⟨S, hS⟩ := hZ
    refine ⟨S, ?_⟩
    have h1 : Set.range D.h = (Submodule.span ℤ (S : Set Ω) : Set Ω) := by
      rw [hS]; rfl
    rw [h1, Submodule.span_span_of_tower]
  exact (hA.sup (D.om_lat.fg.map _)).map _
