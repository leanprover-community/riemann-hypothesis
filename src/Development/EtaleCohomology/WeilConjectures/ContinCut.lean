module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)

namespace LateralTheory.EWeil.ContinCut

universe u v

def Chev : Prop := ∀ (l : ℕ) [Fact l.Prime] (M : Type u) [AddCommGroup M] [Module ℤ_[l] M] [Module.Finite ℤ_[l] M]
  (K : ℕ → Submodule ℤ_[l] M), Antitone K → (∀ x, (∀ k, x ∈ K k) → x = 0) →
  ∀ N : ℕ, ∃ k, ∀ y ∈ K k, ∃ z : M, y = (l : ℤ_[l]) ^ N • z

def AbsCont : Prop := ∀ (l : ℕ) [Fact l.Prime] (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type u) [AddCommGroup M] [Module ℤ_[l] M] [Module.Finite ℤ_[l] M] (ρ : Representation ℤ_[l] G M)
  (K : ℕ → Submodule ℤ_[l] M), Antitone K → (∀ x, (∀ k, x ∈ K k) → x = 0) →
  (∀ (x : M) (k : ℕ), IsOpen {g : G | ρ g x - x ∈ K k}) →
  ∀ (φ : M →ₗ[ℤ_[l]] ℚ_[l]) (x : M), Continuous fun g => φ (ρ g x)

def evk (l : ℕ) [Fact l.Prime] (E : Spc) (n i : ℤ) (k : ℕ) : Hl l E n i →ₗ[ℤ_[l]] HtL l k E n i :=
  (LinearMap.proj (R := ℤ_[l]) (φ := fun k => HtL l k E n i) k).comp (HlSub l E n i).subtype

theorem evk_apply (l : ℕ) [Fact l.Prime] (E : Spc) (n i : ℤ) (k : ℕ) (x : Hl l E n i) : evk l E n i k x = x.1 k := rfl

theorem evk_anti (l : ℕ) [Fact l.Prime] (E : Spc) (n i : ℤ) : Antitone fun k => LinearMap.ker (evk l E n i k) := by
  intro a b hab x hx
  simp only [LinearMap.mem_ker, evk_apply] at hx ⊢
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => exact hx
  | succ d ih =>
    apply ih (Nat.le_add_right _ _)
    have h2 : red (l ^ (a + d + 1)) (l ^ (a + d)) E n i (x.1 (a + d + 1)) = x.1 (a + d) := x.2 (a + d)
    have h3 : (x.1 (a + d + 1) : Ht (l ^ (a + d + 1)) E n i) = 0 := hx
    rw [← h2, h3]; exact map_zero (red (l ^ (a + d + 1)) (l ^ (a + d)) E n i)

end LateralTheory.EWeil.ContinCut
