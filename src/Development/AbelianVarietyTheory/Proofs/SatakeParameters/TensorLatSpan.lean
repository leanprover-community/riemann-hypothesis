module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PosOkId
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardWeylLatticesFockDual
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting

@[expose] public section

open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

noncomputable section

namespace GlobalTheory.StdBaseChange

def pureSet (K : Type) [CommRing K] {S : Type} [Fintype S] {k n : ℕ}
    (A : S → Set (MvPolynomial (Fin k × Fin n) K)) : Set (MvPolynomial (S × (Fin k × Fin n)) K) :=
  {P | ∃ F : S → MvPolynomial (Fin k × Fin n) K, (∀ s, F s ∈ A s) ∧ P = ∏ s, blockEmb K s (F s)}

theorem tensorLat_span (R K : Type) [CommRing R] [CommRing K] [Algebra R K] {S : Type} [Fintype S] {k n : ℕ}
    (A : S → Set (MvPolynomial (Fin k × Fin n) K)) :
    tensorLat R K (fun s => Submodule.span R (A s)) = Submodule.span R (pureSet K A) := by
  classical
  apply le_antisymm
  · unfold tensorLat
    rw [Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    have h1 : ∀ s, blockEmb K s (F s) ∈ Submodule.span R (blockEmb K s '' A s) := fun s =>
      Submodule.apply_mem_span_image_of_mem_span ((blockEmb K s).toLinearMap.restrictScalars R) (hF s)
    have h2 : ∀ t : Finset S, ∏ s ∈ t, blockEmb K s (F s) ∈ ∏ s ∈ t, Submodule.span R (blockEmb K s '' A s) := by
      intro t
      induction t using Finset.induction_on with
      | empty =>
        rw [Finset.prod_empty, Finset.prod_empty]
        exact Submodule.one_le.mp le_rfl
      | insert a t ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha]
        exact Submodule.mul_mem_mul (h1 a) ih
    have h3 := h2 Finset.univ
    rw [Submodule.prod_span] at h3
    refine Submodule.span_mono ?_ h3
    intro P hP
    obtain ⟨G, hG, rfl⟩ := (Set.mem_fintype_prod _ _).mp hP
    choose F' hF' hFG using hG
    exact ⟨F', hF', by simp only [hFG]⟩
  · refine Submodule.span_mono ?_
    rintro _ ⟨F, hF, rfl⟩
    exact ⟨F, fun s => Submodule.subset_span (hF s), rfl⟩

theorem image_pureSet {K L : Type} [CommRing K] [CommRing L] (φ : K →+* L) {S : Type} [Fintype S] {k n : ℕ}
    (A : S → Set (MvPolynomial (Fin k × Fin n) K)) :
    MvPolynomial.map φ '' pureSet K A = pureSet L fun s => MvPolynomial.map φ '' A s := by
  have h : ∀ F : S → MvPolynomial (Fin k × Fin n) K,
      MvPolynomial.map φ (∏ s, blockEmb K s (F s)) = ∏ s, blockEmb L s (MvPolynomial.map φ (F s)) := by
    intro F
    rw [map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    simp only [blockEmb, map_rename]
  ext P
  constructor
  · rintro ⟨_, ⟨F, hF, rfl⟩, rfl⟩
    exact ⟨_, fun s => ⟨F s, hF s, rfl⟩, h F⟩
  · rintro ⟨G, hG, rfl⟩
    choose F hF hFG using hG
    exact ⟨_, ⟨F, hF, rfl⟩, by rw [h]; simp only [hFG]⟩

theorem span_map_span {R K O L σ : Type} [CommRing R] [CommRing K] [Algebra R K] [CommRing O] [CommRing L] [Algebra O L]
    (φ : K →+* L) (ψ : R →+* O) (h : ∀ r, algebraMap O L (ψ r) = φ (algebraMap R K r)) (T : Set (MvPolynomial σ K)) :
    Submodule.span O (MvPolynomial.map φ '' (Submodule.span R T : Set (MvPolynomial σ K))) =
      Submodule.span O (MvPolynomial.map φ '' T) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul a y _ hy =>
      have e : MvPolynomial.map φ (a • y) = ψ a • MvPolynomial.map φ y := by
        rw [← algebraMap_smul K a y, ← algebraMap_smul L (ψ a), smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C, h]
      rw [e]
      exact Submodule.smul_mem _ _ hy
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem dualWeyl_map (R K : Type) [CommRing R] [IsDomain R] [CommRing K] [Algebra R K] (n : ℕ) (ν : Fin n → ℕ) :
    (dualWeyl R n n ν).map (mapAlgHom (Algebra.ofId R K)).toLinearMap = Submodule.span R (StdDual.bidSet K n ν) := by
  rw [StdDual.dualWeyl_eq, Submodule.map_span, ← StdDual.image_bidSet (algebraMap R K)]
  rfl

theorem weyl_map (R K : Type) [CommRing R] [CommRing K] [Algebra R K] (n : ℕ) (ν : Fin n → ℕ) :
    (weyl R n n le_rfl ν).map (mapAlgHom (Algebra.ofId R K)).toLinearMap = Submodule.span R (StdDual.wordSet K n ν) := by
  rw [StdDual.weyl_eq, Submodule.map_span, ← StdDual.image_wordSet (algebraMap R K)]
  rfl

theorem std_baseChange : ∀ (O Kf K ι : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] [Field K] [NumberField K] [Fintype ι] (eK : K →+* Kf) (ψ : 𝓞 K →+* O), (∀ r, algebraMap O Kf (ψ r) = eK r) → ∀ (n : ℕ) (lam : ι → DomWeight n), Submodule.span O (MvPolynomial.map eK '' (nabStd K lam : Set (Pol K ι n))) = (tensorLat O Kf fun τ => stdN O Kf n (lam τ).natW) ∧ Submodule.span O (MvPolynomial.map eK '' (delStd K lam : Set (Pol K ι n))) = (tensorLat O Kf fun τ => stdD O Kf n (lam τ).natW) := by
  intro O Kf K ι _ _ _ _ _ _ _ eK ψ h n lam
  constructor
  · have e : nabStd K lam = tensorLat (𝓞 K) K fun τ => Submodule.span (𝓞 K) (StdDual.bidSet K n (lam τ).natW) := by
      unfold nabStd
      congr 1
      funext τ
      exact dualWeyl_map (𝓞 K) K n (lam τ).natW
    rw [e, tensorLat_span, span_map_span eK ψ h, image_pureSet]
    simp only [stdN, dualWeyl_map, StdDual.image_bidSet]
    rw [tensorLat_span]
  · have e : delStd K lam = tensorLat (𝓞 K) K fun τ => Submodule.span (𝓞 K) (StdDual.wordSet K n (lam τ).natW) := by
      unfold delStd
      congr 1
      funext τ
      exact weyl_map (𝓞 K) K n (lam τ).natW
    rw [e, tensorLat_span, span_map_span eK ψ h, image_pureSet]
    simp only [stdD, weyl_map, StdDual.image_wordSet]
    rw [tensorLat_span]

end GlobalTheory.StdBaseChange
