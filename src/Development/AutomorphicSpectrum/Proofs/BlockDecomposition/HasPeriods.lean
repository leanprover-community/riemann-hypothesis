module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.CompanionTheory.LTHodge

variable {l : ℕ} [Fact l.Prime]

def lineRep {K LL : FinExt l} (ψ : ↥(GK K) →* (↥LL.1)ˣ) :
    Representation ↥LL.1 ↥(GK K) (Fin 1 → ↥LL.1) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin 1) (Fin 1) ↥LL.1 ≃ₐ[↥LL.1] _) : _ →* _).comp
    ((Units.coeHom _).comp ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL.1).comp ψ))

def ltSeries {K : FinExt l} (π : ↥(OL K)) : PowerSeries ↥(OL K) :=
  PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ Nat.card (↥(OL K) ⧸ Ideal.span {π})

def IsLTChar (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) : Prop :=
  ∃ (π : ↥(OL K)) (z : ℕ → Om l), Irreducible π ∧ z 0 = 0 ∧ z 1 ≠ 0 ∧
    (∀ n, z (n + 1) ^ Nat.card (↥(OL K) ⧸ Ideal.span {π}) +
      (((π : ↥K.1) : Om l)) * z (n + 1) = z n) ∧
    ∀ (g : ↥(GK K)) (φ : PowerSeries ↥(OL K)), PowerSeries.constantCoeff φ = 0 →
      ((PowerSeries.coeff 1 φ : ↥(OL K)) : ↥K.1) = ((χ g : (↥K.1)ˣ) : ↥K.1) →
      PowerSeries.subst φ (ltSeries π) = PowerSeries.subst (ltSeries π) φ →
      ∀ n, HasSum (fun k : ℕ => (((PowerSeries.coeff k φ : ↥(OL K)) : ↥K.1) : Om l) * z n ^ k)
        ((g : GQ l) (z n))

def HasPeriods (P : LocPrime l) (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) : Prop :=
  ∀ μ : ↥K.1 →ₐ[ℚ_[l]] Om l, ∃ y : P.R.BdR,
    (∀ (g : GQ l) (hg : g ∈ GK K), (∀ x : ↥K.1, g (μ x) = μ x) →
      P.actQdR g y = algebraMap (Om l) P.R.BdR (μ ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1)) * y) ∧
    (μ = K.1.val → y ∈ (P.PD K).Fil 1 ∧ y ∉ (P.PD K).Fil 2) ∧
    (μ ≠ K.1.val → y ∈ (P.PD K).Fil 0 ∧ y ∉ (P.PD K).Fil 1)

end GlobalTheory.CompanionTheory.LTHodge
