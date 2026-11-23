module

public import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedProjectorOrthogonalOfUnitaryAction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField

theorem _root_.GlobalTheory.T.twistedProjector_orthogonal_of_unitary_action : ∀ {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
    {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
    {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    {G0 : Type} [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G0) (eC : G0 → LL), ∀ σ : LL →+* ℂ, A.eOp eC ∘ₗ A.eOp eC = A.eOp eC →
    (∀ g x y, inner ℂ (A.j σ (A.ρ g x)) (A.j σ (A.ρ g y)) = inner ℂ (A.j σ x) (A.j σ y)) →
    (∀ g, σ (eC g⁻¹) = starRingEnd ℂ (σ (eC g))) →
    ∀ x y, ‖A.j σ (A.eOp eC x + (y - A.eOp eC y))‖ ^ 2 = ‖A.j σ (A.eOp eC x)‖ ^ 2 + ‖A.j σ (y - A.eOp eC y)‖ ^ 2 := by
  first | exact @GlobalTheory.twistedProjector_orthogonal_of_unitary | exact GlobalTheory.twistedProjector_orthogonal_of_unitary | (intros; apply GlobalTheory.twistedProjector_orthogonal_of_unitary <;> assumption)
