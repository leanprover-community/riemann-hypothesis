module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
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

namespace GlobalTheory.CompanionTheory.Ar.Num

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ}

def NormalCharts (x : (Σ k, ι k) → Ω) : Prop :=
  ∀ c, mseg x c ≠ 0 → IsIntegrallyClosedIn (chartRing O (mseg x) c) Ω

structure IsLatticeFamily (x : (Σ k, ι k) → Ω) (p : ℕ) (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg)
    (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s) : Prop where
  famM : IsLatFamily O x fun c => (D c).M
  fam : ∀ τ, IsLatFamily O x (fun c => (D c).lie τ) ∧ IsLatFamily O x (fun c => (D c).W τ) ∧
    IsLatFamily O x (fun c => (D c).om τ) ∧ IsLatFamily O x (fun c => (D c).omHT τ) ∧
    IsLatFamily O x (fun c => (D c).Gam τ) ∧ IsLatFamily O x (fun c => (D c).Del τ) ∧
    IsLatFamily O x (fun c => (D c).Th τ)
  char : (p : O) ≠ 0 ∧ (∃ u : O, IsUnit u ∧ w ^ (p - 1) = u * (p : O)) ∧ ¬ IsUnit (p : O) ∧ (0 : F) ≠ 1 ∧
    ∀ τ, χ τ 0 = 0 ∧ χ τ 1 = 1
  base : ∀ c, mseg x c ≠ 0 → (D c).Base (chartRing O (mseg x) c) p (algebraMap O Ω w)
  test : ∀ c, mseg x c ≠ 0 → (D c).TestFacts (chartRing O (mseg x) c) p (algebraMap O Ω w)
    (fun τ a => algebraMap O Ω (χ τ a)) φ

def pullFamily {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] (x : (Σ k, ι k) → Ω)
    (z : (Σ k, ι' k) → Ω) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s) :
    (∀ k : K ⊕ K', Sum.elim ι ι' k) → LieLatticeData Ω F n Sg r s :=
  fun c => (D (restrictChart c)).bc (chartRing O (mseg (joinCoord x z)) c)

def HasBundles (x : (Σ k, ι k) → Ω) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s)
    (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω))
    (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)) : Prop :=
  ∀ τ c, mseg x c ≠ 0 → (Lie τ).lat c = (D c).lie τ ∧ (W τ).lat c = (D c).W τ ∧
    (Om τ).lat c = (D c).om τ ∧ (OmHT τ).lat c = (D c).omHT τ

def CkRelations (x : (Σ k, ι k) → Ω) (d p : ℕ) (φ : Equiv.Perm Sg) {VL VO : Sg → Type}
    [∀ τ, AddCommGroup (VL τ)] [∀ τ, Module Ω (VL τ)] [∀ τ, AddCommGroup (VO τ)] [∀ τ, Module Ω (VO τ)]
    (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (VL τ))
    (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (VO τ)) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ),
    Q.IsHomogeneous (d + 1 - k) → ∃ h : Sg → ℝ,
      (∀ τ, ((ck O x d (r τ) (Lie τ) (W τ) k L Q : ℤ) : ℝ) + ((ck O x d (s τ) (Om τ) (OmHT τ) k L Q : ℤ) : ℝ) =
        h τ - (k : ℝ) * ((rootNum O x d (r τ) (Lie τ) (psum (Fin (r τ)) ℤ (k - 1)) L Q (p : O) : ℤ) : ℝ) /
          ((p : ℝ) - 1)) ∧
      ∀ τ, (p : ℝ) ^ k * h τ = h (φ τ) +
        (k : ℝ) * ((rootNum O x d (r (φ τ)) (Lie (φ τ)) (psum (Fin (r (φ τ))) ℤ (k - 1)) L Q (p : O) : ℤ) : ℝ)

end GlobalTheory.CompanionTheory.Ar.Num
