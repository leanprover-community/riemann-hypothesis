module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormGLContinuous
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormEqZeroOfWhittakerVanishing
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalSphericalVectorOfSatakeFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAutomorphicFormFixedOfLocallyIntegralFixed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SatakeComb
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Spherical
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SphericalA
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup
import GroundTheory.AutomorphicForms.MultiplicityOne.Equivariance

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicGLAgreeOutsideTrivialOnFinset, Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicGLMemIntegralCofinitePlaces, Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaDecompositionAdicCompletionGLDiagonalPowe, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSphericalCuspFormWhittakerNeZero

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicGLAgreeOutsideTrivialOnFinset =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicGLAgreeOutsideTrivialOnFinset", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe\nimport Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds\nimport Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SatakeComb\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix

namespace GlobalTheory

theorem outsideS_elt : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (k : GL (Fin a) (Af E)), ∃ k' : GL (Fin a) (Af E), (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k' = GeneralLinearGroup.map (pLoc E w) k) ∧ ∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k' = 1 := by
  intro E _ _ a S k
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨k, fun w _ => rfl, fun w hw => absurd hw (Finset.notMem_empty w)⟩
  | insert w S hwS ih =>
    obtain ⟨k', h1, h2⟩ := ih
    refine ⟨k' * (locGL E a w (GeneralLinearGroup.map (pLoc E w) k'))⁻¹, ?_, ?_⟩
    · intro v hv
      have hvw : v ≠ w := fun e => hv (e ▸ Finset.mem_insert_self _ _)
      rw [map_mul, map_inv, pLoc_locGL_of_ne hvw, inv_one, mul_one]
      exact h1 v (fun h => hv (Finset.mem_insert_of_mem h))
    · intro v hv
      rw [map_mul, map_inv]
      by_cases hvw : v = w
      · subst hvw; rw [pLoc_locGL, mul_inv_cancel]
      · rw [pLoc_locGL_of_ne hvw, inv_one, mul_one]
        exact h2 v ((Finset.mem_insert.1 hv).resolve_left hvw)

end GlobalTheory
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicGLAgreeOutsideTrivialOnFinset =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicGLMemIntegralCofinitePlaces =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicGLMemIntegralCofinitePlaces", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU\nimport Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix

namespace GlobalTheory.GLFinPlaces

theorem gl_mem_int_cofinite (E : Type) [Field E] [NumberField E] (a : ℕ) (k : GL (Fin a) (Af E)) :
    {w : HeightOneSpectrum (𝓞 E) | GeneralLinearGroup.map (pLoc E w) k ∉ KGL w (n := a)}.Finite := by
  have hent : ∀ M : Matrix (Fin a) (Fin a) (Af E), ∀ᶠ w in Filter.cofinite,
      ∀ i j, (M i j) w ∈ w.adicCompletionIntegers E := by
    intro M
    rw [Filter.eventually_all]; intro i
    rw [Filter.eventually_all]; intro j
    exact (M i j).2
  have h := (hent (k : Matrix (Fin a) (Fin a) (Af E))).and (hent ((k⁻¹ : GL (Fin a) (Af E)) : Matrix (Fin a) (Fin a) (Af E)))
  rw [Filter.eventually_cofinite] at h
  refine h.subset ?_
  intro w hw
  simp only [Set.mem_setOf_eq] at hw ⊢
  intro hg
  apply hw
  have key : ∀ M : Matrix (Fin a) (Fin a) (Af E), (∀ i j, (M i j) w ∈ w.adicCompletionIntegers E) →
      M.map (pLoc E w) ∈ (RingHom.mapMatrix (m := Fin a) (Ov E w).subtype).range := by
    intro M hM
    exact ⟨Matrix.of fun i j => (⟨(M i j) w, hM i j⟩ : Ov E w), by ext i j; rfl⟩
  refine P.glint_mem_range_of_integral _ _ ?_ ?_
  · exact key _ hg.1
  · rw [← map_inv]
    exact key _ hg.2

end GlobalTheory.GLFinPlaces
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicGLMemIntegralCofinitePlaces =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaDecompositionAdicCompletionGLDiagonalPowe =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaDecompositionAdicCompletionGLDiagonalPowe", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU\nimport Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero\nimport Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Spherical\nimport Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SphericalA\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix

noncomputable section

namespace GlobalTheory.IwasawaGL

theorem diagPow_val {K : Type} [Field K] {n : ℕ} (ϖ : Kˣ) (l : Fin n → ℕ) :
    ((GlobalTheory.JSW.diagPow ϖ l : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal (fun i => ((ϖ ^ l i : Kˣ) : K)) := rfl

theorem exists_unit_part (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifV E w (ϖ : w.adicCompletion E)) (x : w.adicCompletion E)
    (hx : x ≠ 0) :
    ∃ e : ℤ, Valued.v (x * ((ϖ ^ (-e) : (w.adicCompletion E)ˣ) : w.adicCompletion E)) = 1 := by
  have h0 : Valued.v x ≠ 0 := by simpa using hx
  obtain ⟨γ, hγ⟩ := WithZero.ne_zero_iff_exists.1 h0
  refine ⟨-Multiplicative.toAdd γ, ?_⟩
  rw [map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ, ← hγ, neg_neg,
    ← WithZero.coe_zpow, ← WithZero.coe_mul]
  rw [show (1 : WithZero (Multiplicative ℤ)) = ((1 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) from rfl]
  congr 1
  apply Multiplicative.toAdd.injective
  simp

theorem iwasawa_diagPow : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ g : GL (Fin a) (w.adicCompletion E), ∃ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a), ∃ (N : ℕ) (l : Fin a → ℕ), ∃ k ∈ KGL w (n := a), g = u * GlobalTheory.JSW.diagPow ϖ⁻¹ (fun _ => N) * GlobalTheory.JSW.diagPow ϖ l * k := by
  intro E _ _ a w ϖ hϖ g
  obtain ⟨b, k, hb, hk, rfl⟩ := Formalism.UG.P.spherical_iwasawa E w g
  have hd : ∀ i, (b : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i i ≠ 0 :=
    Formalism.UG.P.spherical_diag_ne_zero b hb
  choose e he using fun i => exists_unit_part E w ϖ hϖ _ (hd i)
  let c : Fin a → w.adicCompletion E := fun i =>
    (b : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i i * ((ϖ ^ (-e i) : (w.adicCompletion E)ˣ) : w.adicCompletion E)
  have hc0 : ∀ i, c i ≠ 0 := fun i => mul_ne_zero (hd i) (Units.ne_zero _)
  have hcO : ∀ i, c i ∈ Ov E w := fun i => (he i).le
  have hcO' : ∀ i, (c i)⁻¹ ∈ Ov E w := fun i => by
    show Valued.v (c i)⁻¹ ≤ 1
    rw [map_inv₀, he i, inv_one]
  let Dc : GL (Fin a) (w.adicCompletion E) :=
    ⟨Matrix.diagonal c, Matrix.diagonal (fun i => (c i)⁻¹),
      by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact mul_inv_cancel₀ (hc0 i),
      by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact inv_mul_cancel₀ (hc0 i)⟩
  have hDc : Dc ∈ KGL w (n := a) := by
    refine Formalism.UG.P.glint_mem_range_of_integral (Ov E w) Dc
      ⟨Matrix.diagonal (fun i => (⟨c i, hcO i⟩ : Ov E w)), ?_⟩
      ⟨Matrix.diagonal (fun i => (⟨(c i)⁻¹, hcO' i⟩ : Ov E w)), ?_⟩
    · ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply, Dc]
      split_ifs <;> simp
    · ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply, Dc, Units.inv_mk]
      split_ifs <;> simp
  let N : ℕ := ∑ i, (e i).natAbs
  let l : Fin a → ℕ := fun i => (e i + N).toNat
  have hexp : ∀ i, ((ϖ⁻¹) ^ N * ϖ ^ (l i) : (w.adicCompletion E)ˣ) = ϖ ^ (e i) := by
    intro i
    have hle : (e i).natAbs ≤ N :=
      Finset.single_le_sum (f := fun j => (e j).natAbs) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    have h1 : -((e i).natAbs : ℤ) ≤ e i := by rw [Int.natCast_natAbs]; exact neg_abs_le _
    have h2 : ((e i).natAbs : ℤ) ≤ N := by exact_mod_cast hle
    have hl : ((l i : ℕ) : ℤ) = e i + N := Int.toNat_of_nonneg (by omega)
    rw [inv_pow, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_neg, ← _root_.zpow_add, hl]
    congr 1; ring
  have hT : ((GlobalTheory.JSW.diagPow ϖ⁻¹ (fun _ => N) * GlobalTheory.JSW.diagPow ϖ l * Dc : GL (Fin a) (w.adicCompletion E)) :
      Matrix (Fin a) (Fin a) (w.adicCompletion E)) =
      Matrix.diagonal (fun i => (b : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i i) := by
    rw [Units.val_mul, Units.val_mul, diagPow_val, diagPow_val]
    change Matrix.diagonal _ * Matrix.diagonal _ * Matrix.diagonal c = _
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; funext i
    rw [← Units.val_mul, hexp i]
    simp only [c]
    rw [mul_left_comm, ← Units.val_mul, ← _root_.zpow_add, add_neg_cancel, zpow_zero, Units.val_one, mul_one]
  let u : GL (Fin a) (w.adicCompletion E) := b * (GlobalTheory.JSW.diagPow ϖ⁻¹ (fun _ => N) * GlobalTheory.JSW.diagPow ϖ l * Dc)⁻¹
  have hu : u * (GlobalTheory.JSW.diagPow ϖ⁻¹ (fun _ => N) * GlobalTheory.JSW.diagPow ϖ l * Dc) = b := by
    simp only [u]; group
  have hmat : (u : Matrix (Fin a) (Fin a) (w.adicCompletion E)) *
      Matrix.diagonal (fun i => (b : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i i) = b := by
    rw [← hT, ← Units.val_mul, hu]
  have hent : ∀ i j, (u : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j *
      (b : Matrix (Fin a) (Fin a) (w.adicCompletion E)) j j = (b : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j := by
    intro i j
    have := congrFun (congrFun hmat i) j
    rwa [Matrix.mul_diagonal] at this
  have hmem : u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a) := by
    refine (GlobalTheory.SmGL.mem_unipB _).2 ⟨fun i j hij => ?_, fun i => ?_⟩
    · have h := hent i j
      rw [hb hij] at h
      exact (mul_eq_zero.1 h).resolve_right (hd j)
    · exact mul_right_cancel₀ (hd i) (by rw [one_mul]; exact hent i i)
  refine ⟨u, hmem, N, l, Dc * k, Subgroup.mul_mem _ hDc hk, ?_⟩
  simp only [u]
  group

end GlobalTheory.IwasawaGL
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaDecompositionAdicCompletionGLDiagonalPowe =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSphericalCuspFormWhittakerNeZero =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSphericalCuspFormWhittakerNeZero", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormGLContinuous\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormEqZeroOfWhittakerVanishing\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicGLAgreeOutsideTrivialOnFinset\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalSphericalVectorOfSatakeFamily\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicGLMemIntegralCofinitePlaces\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaDecompositionAdicCompletionGLDiagonalPowe\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAutomorphicFormFixedOfLocallyIntegralFixed\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed\nimport Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup\nimport GroundTheory.AutomorphicForms.MultiplicityOne.Equivariance\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff

noncomputable section

namespace GlobalTheory.JSW.NzSph

theorem finite_bad (E : Type) [Field E] [NumberField E] (a : ℕ) (k : GL (Fin a) (Af E)) :
    {w : HeightOneSpectrum (𝓞 E) | GeneralLinearGroup.map (pLoc E w) k ∉ KGL w (n := a)}.Finite :=
  _root_.GlobalTheory.GLFinPlaces.gl_mem_int_cofinite E a k

theorem exists_outside (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (k : GL (Fin a) (Af E)) : ∃ k' : GL (Fin a) (Af E),
      (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k' = GeneralLinearGroup.map (pLoc E w) k) ∧
      ∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k' = 1 :=
  _root_.GlobalTheory.outsideS_elt E a S k

theorem local_decomp (E : Type) [Field E] [NumberField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifV E w (ϖ : w.adicCompletion E)) (g : GL (Fin a) (w.adicCompletion E)) :
    ∃ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a), ∃ (N : ℕ) (l : Fin a → ℕ), ∃ k ∈ KGL w (n := a),
      g = u * GlobalTheory.JSW.diagPow ϖ⁻¹ (fun _ => N) * GlobalTheory.JSW.diagPow ϖ l * k :=
  _root_.GlobalTheory.IwasawaGL.iwasawa_diagPow E a w ϖ hϖ g

theorem act_fin_eq_of_outside (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a)
    (hφ : IsAutForm φ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ w ∉ S, ∀ k ∈ KGL w (n := a), act (.fin (locGL E a w k)) φ = φ) (k : GL (Fin a) (Af E))
    (hk : ∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k ∈ KGL w (n := a))
    (hk1 : ∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k = 1) : act (.fin k) φ = φ :=
  _root_.GlobalTheory.CuspRep.fixed_of_locFixed E a φ hφ S hS k hk hk1

end GlobalTheory.JSW.NzSph

namespace GlobalTheory.JSW.NzSph

open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.MultiplicityOne

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem map_pLoc_pFin (w : HeightOneSpectrum (𝓞 E)) (g : GA E a) :
    GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) =
      GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g := by
  ext; rfl

theorem comp_finGL (v : HeightOneSpectrum (𝓞 E)) (h : GL (Fin a) (Af E)) :
    GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (finGL E a h) = GeneralLinearGroup.map (pLoc E v) h := by
  rw [finGL, map_cornerGL_of_hom (sFin E) ((pLoc E v).comp (pFin E)) (pLoc E v) (fun x => rfl)]

theorem diagPow_const_comm {K : Type} [CommRing K] {n : ℕ} (c : Kˣ) (N : ℕ) (h : GL (Fin n) K) :
    GlobalTheory.JSW.diagPow c (fun _ : Fin n => N) * h = h * GlobalTheory.JSW.diagPow c (fun _ : Fin n => N) := by
  ext i j
  simp [GlobalTheory.JSW.diagPow, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

variable [_root_.NumberField.IsTotallyComplex E]

theorem whit_act_fin (φ : Sm E a) (k : GL (Fin a) (Af E)) (y : GA E a) :
    whit (act (.fin k) φ).1 y = whit φ.1 (y * finGL E a k) := by
  rw [whit_mul_right]; rfl

theorem act_fin_mul (k k' : GL (Fin a) (Af E)) (φ : Sm E a) :
    act (.fin (k * k')) φ = act (.fin k) (act (.fin k') φ) := by
  show finRep E a (k * k') φ = finRep E a k (finRep E a k' φ)
  rw [map_mul]; rfl

theorem exists_whittaker_ne_zero_induction_bad_places (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hψ : ∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w)
    (π : CuspSub E a) (α : HeightOneSpectrum (𝓞 E) → Fin a → ℂˣ)
    (hα : ∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) (T : Finset (HeightOneSpectrum (𝓞 E))) :
    ∀ φ ∈ π.V, (∀ w ∉ S, ∀ k ∈ KGL w (n := a), act (.fin (locGL E a w k)) φ = φ) → ∀ g : GA E a,
      (∀ w ∉ S, w ∉ T → GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g ∈ KGL w (n := a)) → whit φ.1 g ≠ 0 →
      ∃ φ ∈ π.V, (∀ w ∉ S, ∀ k ∈ KGL w (n := a), act (.fin (locGL E a w k)) φ = φ) ∧
        ∃ x ∈ GlobalTheory.JSW.supS (E := E) (a := a) S, whit φ.1 x ≠ 0 := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro φ hφV hφ g hg hW
    obtain ⟨k, hk1, hk2⟩ := exists_outside E a S (GeneralLinearGroup.map (pFin E) g)
    have hinv : act (.fin k) φ = φ := act_fin_eq_of_outside E a φ (π.cusp φ hφV).1 S hφ k
      (fun w hw => by rw [hk1 w hw, map_pLoc_pFin]; exact hg w hw (Finset.notMem_empty w)) hk2
    refine ⟨φ, hφV, hφ, g * (finGL E a k)⁻¹, fun w hw => ?_, ?_⟩
    · rw [map_mul, map_inv, comp_finGL, hk1 w hw, map_pLoc_pFin, mul_inv_cancel]
    · have e : g = g * (finGL E a k)⁻¹ * finGL E a k := by group
      rw [e, ← whit_act_fin, hinv] at hW
      exact hW
  | insert w T hwT ih =>
    intro φ hφV hφ g hg hW
    by_cases hwS : w ∈ S
    · refine ih φ hφV hφ g (fun v hv hvT => hg v hv ?_) hW
      rw [Finset.mem_insert, not_or]
      exact ⟨fun h => hv (h ▸ hwS), hvT⟩
    obtain ⟨ϖ0, hϖ0⟩ := exists_isUnifV (E := E) w
    have hne : ϖ0 ≠ 0 := fun h => by simp [IsUnifV, h] at hϖ0
    let ϖ : (w.adicCompletion E)ˣ := Units.mk0 ϖ0 hne
    have hϖ : IsUnifV E w (ϖ : w.adicCompletion E) := hϖ0
    let gw := GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g
    obtain ⟨u, hu, N, l, k, hk, hdec⟩ := local_decomp E a w ϖ hϖ gw
    let z := GlobalTheory.JSW.diagPow ϖ⁻¹ (fun _ : Fin a => N)
    let d := GlobalTheory.JSW.diagPow ϖ l
    let F : GL (Fin a) (w.adicCompletion E) →* GA E a := (finGL E a).comp (locGL E a w)
    have hF : ∀ h, F h = finGL E a (locGL E a w h) := fun h => rfl
    let y := g * (F gw)⁻¹
    have hyw : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y = 1 := by
      show GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (g * (finGL E a (locGL E a w gw))⁻¹) = 1
      rw [map_mul, map_inv, comp_finGL, pLoc_locGL]; exact mul_inv_cancel _
    have hyv : ∀ v, v ≠ w → GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) y =
        GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) g := by
      intro v hv
      show GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (g * (finGL E a (locGL E a w gw))⁻¹) = _
      rw [map_mul, map_inv, comp_finGL, pLoc_locGL_of_ne hv, inv_one, mul_one]
    have hg' : g = y * F u * F z * F d * F k := by
      have : F gw = F u * F z * F d * F k := by
        rw [hdec, map_mul, map_mul, map_mul]
      calc g = y * F gw := by simp only [y]; group
        _ = _ := by rw [this]; simp only [mul_assoc]
    have hcont : Continuous φ.1 := (π.cusp _ hφV).1.continuous
    have hleft : AutomorphicForm.IsLeftInvariant φ.1 := fun γ x => by
      rw [show AdelicGLn.diagonal E a γ = ratGL E a γ from Units.ext (Matrix.ext fun _ _ => rfl)]
      exact (π.cusp _ hφV).1.left γ x

    have h1 : whit φ.1 (y * F u * F z * F d) ≠ 0 := by
      rw [hg', hF k, ← whit_act_fin, hφ w hwS k hk] at hW
      exact hW

    have h2 : whit φ.1 (y * F z * F d) ≠ 0 := by
      have e : y * F u * F z * F d = F u * (y * F z * F d) := by
        rw [hF u, commute_finGL_locGL w hyw u]; group
      rw [e, hF u, finGL_locGL_eq_uGL w hu, whit, whittaker_uGL_mul hcont hleft] at h1
      exact right_ne_zero_of_mul h1

    let φ₁ := act (.fin (locGL E a w z)) φ
    have hφ₁V : φ₁ ∈ π.V := π.stable _ φ hφV
    have hφ₁ : ∀ v ∉ S, ∀ k' ∈ KGL v (n := a), act (.fin (locGL E a v k')) φ₁ = φ₁ := by
      intro v hv k' hk'
      have hc : locGL E a v k' * locGL E a w z = locGL E a w z * locGL E a v k' := by
        by_cases hvw : v = w
        · subst hvw; rw [← map_mul, ← map_mul, diagPow_const_comm]
        · exact (GlobalTheory.CuspRep.LocSph.comm_locGL v (locGL E a w z) (pLoc_locGL_of_ne hvw z) k').symm
      simp only [φ₁]
      rw [← act_fin_mul, hc, act_fin_mul, hφ v hv k' hk']
    have h3 : whit φ₁.1 (y * F d) ≠ 0 := by
      have e : y * F z * F d = y * F d * F z := by
        rw [mul_assoc y (F z), mul_assoc y (F d), ← map_mul, ← map_mul, diagPow_const_comm]
      rw [e, hF z, ← whit_act_fin] at h2
      exact h2
    have h4 : whit φ₁.1 y ≠ 0 := by
      have := GlobalTheory.JSW.whit_mul_locGL_diagPow E a π w (α w) (hψ w hwS) (hα w hwS) φ₁ hφ₁V (hφ₁ w hwS) y hyw ϖ hϖ l
      rw [hF d] at h3
      rw [this] at h3
      exact right_ne_zero_of_mul h3
    refine ih φ₁ hφ₁V hφ₁ y (fun v hv hvT => ?_) h4
    by_cases hvw : v = w
    · subst hvw; rw [hyw]; exact one_mem _
    · rw [hyv v hvw]
      exact hg v hv (by rw [Finset.mem_insert, not_or]; exact ⟨hvw, hvT⟩)

theorem exists_sph_whit_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) → ∀ (π : CuspSub E (m + 1)) (α : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ), (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) → ∃ φ ∈ π.V, (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), act (.fin (locGL E (m + 1) w k)) φ = φ) ∧ ∃ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit φ.1 x ≠ 0 := by
  intro E _ _ _ m S hψ π α hα
  obtain ⟨φ₀, hφ₀V, hφ₀0, hφ₀K⟩ := _root_.GlobalTheory.JSW.SphVec.exists_sphVec_of_hasSat E (m + 1) π S (fun w => Finset.univ.val.map (α w)) hα
  obtain ⟨g, hg⟩ : ∃ g, whit φ₀.1 g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ₀0 (_root_.GlobalTheory.JSW.eq_zero_of_whit_eq_zero E (m + 1) φ₀ (π.cusp φ₀ hφ₀V) h)
  have hfin := finite_bad E (m + 1) (GeneralLinearGroup.map (pFin E) g)
  refine exists_whittaker_ne_zero_induction_bad_places S hψ π α hα hfin.toFinset φ₀ hφ₀V hφ₀K g (fun w _ hwT => ?_) hg
  by_contra h
  refine hwT (hfin.mem_toFinset.2 ?_)
  show GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) ∉ KGL w (n := (m + 1))
  rw [map_pLoc_pFin]; exact h

end GlobalTheory.JSW.NzSph
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSphericalCuspFormWhittakerNeZero =====
