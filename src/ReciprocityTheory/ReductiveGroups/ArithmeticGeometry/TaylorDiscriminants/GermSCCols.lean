module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.GermSC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
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

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB

def SCColsSt : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k]
    [Algebra R k], IsRQ (R := R) k → ∀ (J : Submodule R k), (1 : k) ∈ J →
    ∀ (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ (w0 : O), w0 + star w0 = 1 → ∀ (m : ℕ)
    (ι π : Type) [Fintype ι] [Fintype π] [DecidableEq π] (c : ι → π) (s : ι → Bool)
    (ξh : ι → (Fin d → k) × (Fin d → k)) (ψ : ι → Fin d → k),
    (∀ l, ξh l ∈ Hset (R := R) k h) → (∀ l i, ψ l i ∈ J) →
    OppositePairVanishing k c s ξh ξh → OppositePairVanishing k c s (fun l => (0, ψ l)) ξh → OppositePairVanishing k c s ξh (fun l => (0, ψ l)) →
    ∀ (n : ℕ) (P : MvPolynomial (ι × Fin n) k), (∀ mo, P.coeff mo ∈ (algebraMap R k).range) →
    ∀ (e : ℕ), (∀ mo ∈ P.support, ∑ b, pairMin c s (colM mo b) ≤ e) →
    ∀ f : Fin n → PS k 1 d, (∀ b, IntAA (R := R) k (f b)) →
      ∑ mo ∈ P.support, P.coeff mo * ∏ b, constantCoeff (ordNabla k B h m s (fun l => ξh l + (0, ψ l))
        (MvPolynomial.monomial (colM mo b) 1) (liftX k (FB.expS k ((m : k) • B.hL k h w0) * f b))) ∈ J ^ e

def LemmaHColsSt : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k]
    [Algebra R k] (B : FB R d O) (h : PS k 2 d), ev (n := 1) ![0, pt k d 0] h = 0 → ∀ (m : ℕ)
    (ι π : Type) [Fintype ι] [DecidableEq π] (c : ι → π) (s : ι → Bool) (u φ : ι → Fin d → k),
    OppositePairVanishing k c s (fun l => (u l, 0)) (fun l => (u l, 0)) → OppositePairVanishing k c s (fun l => (u l, 0)) (fun l => (0, φ l)) →
    OppositePairVanishing k c s (fun l => (0, φ l)) (fun l => (u l, 0)) →
    ∀ (n : ℕ) (P : MvPolynomial (ι × Fin n) k),
      secondOrder k (fun p q : ι × Fin n => if p.2 = q.2 ∧ c p.1 = c q.1 ∧ s p.1 = true ∧ s q.1 = false then
        (m : k) * betaH k (0, φ p.1) (u q.1, 0) else 0) P = 0 →
    ∀ g : Fin n → PS k 1 d,
      ∑ mo ∈ P.support, P.coeff mo * ∏ b, constantCoeff (ordNabla k B h m s (fun l => (u l, φ l))
          (MvPolynomial.monomial (colM mo b) 1) (liftX k (g b))) =
        ∑ mo ∈ P.support, P.coeff mo * ∏ b, constantCoeff (DpolyOf (B.FK k) u
          (MvPolynomial.monomial (colM mo b) 1) (g b))

end ReciprocityTheory.ChartRestriction.G.TB
