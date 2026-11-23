module

public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapNormCoeff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSecNormCoeffLocal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Polynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.NormalDescent

theorem _root_.GlobalTheory.T.exists_sec_normCoeff_local' : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    {M : LB X}, M.IsLB → ∀ t : (M.pull f).Sec, ∃ u : ∀ k, (lbPow M k).Sec, ∀ x : X,
      ∃ (V : X.Opens) (hV : IsAffineOpen V) (_ : IsDomain Γ(X, V)) (_ : IsIntegrallyClosed Γ(X, V))
        (τ : Γ(Y, f ⁻¹ᵁ V)), x ∈ V ∧ (∀ y : Y, f y ∈ V → (y ∈ nonzeroLocus t ↔ y ∈ Y.basicOpen τ)) ∧
        ∀ (k : ℕ) (z : X), z ∈ V →
          (z ∈ nonzeroLocus (u k) ↔ z ∈ X.basicOpen (normCoeff (f.app V).hom (f.finite_app V hV) τ k)) := by
  first | exact @GlobalTheory.NormalDescent.exists_sec_normCoeff_local | exact GlobalTheory.NormalDescent.exists_sec_normCoeff_local | (intros; apply GlobalTheory.NormalDescent.exists_sec_normCoeff_local <;> assumption)
