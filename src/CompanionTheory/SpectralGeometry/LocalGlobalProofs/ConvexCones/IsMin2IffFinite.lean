module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DicksonExistsFiniteSubfamilyBelow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem isMin2_iff_finite : ∀ (X : Type) [AddCommGroup X] (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (y : X),
    (∀ i x, 0 ≤ u i x x) → ∃ F : Finset X, ∀ B ∈ rcone u,
      (IsMin2 B y ↔ ∀ x ∈ F, B y y ≤ B (y + (x + x)) (y + (x + x))) := by
  intro X _ m u y hu
  obtain ⟨F, hF⟩ := GlobalTheory.dickson_finite_below_every (ι := X) m fun x i => (u i (y + (x + x)) (y + (x + x))).toNat
  refine ⟨F, ?_⟩
  rintro B ⟨t, ht, rfl⟩
  refine ⟨fun h x _ => h x, fun h x => ?_⟩
  obtain ⟨x', hx', hle⟩ := hF x
  refine (h x' hx').trans ?_
  have hval : ∀ a : X, (∑ i, t i • toReal (u i)) a a = ∑ i, t i * (u i a a : ℝ) := fun a => by
    simp [LinearMap.sum_apply]
  simp only [hval]
  refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (ht i)
  have h1 := hle i
  have h2 := hu i (y + (x' + x'))
  have h3 := hu i (y + (x + x))
  simp only at h1
  exact_mod_cast (omega : u i (y + (x' + x')) (y + (x' + x')) ≤ u i (y + (x + x)) (y + (x + x)))

end GlobalTheory.CompanionTheory.Ar.Fan
