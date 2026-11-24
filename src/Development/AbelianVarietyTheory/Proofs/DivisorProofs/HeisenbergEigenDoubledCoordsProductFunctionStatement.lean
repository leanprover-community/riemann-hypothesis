module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenDoubledCoordsProductFunction
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromColsMemLatDbl
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.heisenbergEigen_doubledCoords_productFunction : ∀ {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
    {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (ξ ξ' : E) (JA : Matrix α α E) (JB : Matrix β β E)
    {κ : Type} [Fintype κ] (d : Darboux (symp c ξ JA JB) κ) (dd : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ)),
    IsDblCoord c ξ JA JB d dd → ∀ ψ : AddChar R ℂ, (∀ t, ‖ψ t‖ = 1) → ∀ (Λ : Set (Matrix α β E)) (f : (κ → R) → ℂ),
    (∀ w ∈ Λ, d.rho ψ w f = ψ (⅟(2 : R) * symp c ξ' JA JB w w) • f) →
    ∀ z : Matrix α (β ⊕ β) E, z.toCols₁ ∈ Λ → z.toCols₂ ∈ Λ →
      dd.rho ψ z (boxFun f (fun x => star (f x))) = ψ (⅟(2 : R) * symp c ξ' JA (dbl JB) z z) • boxFun f (fun x => star (f x)) := by
  first | exact @GlobalTheory.DblBoxRho.boxrho | exact GlobalTheory.DblBoxRho.boxrho | (intros; apply GlobalTheory.DblBoxRho.boxrho <;> assumption)
