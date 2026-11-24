module

import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.VanishingIdealConePrimeHomogeneous
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.FieldTheory.IsAlgClosed.Basic
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
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.BaseChangeCA
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Jacobson.Ring

@[expose] public section

open TensorProduct

noncomputable section
namespace GlobalTheory.CxPointsSep

theorem eq_zero_of_forall_algHom {k A : Type} [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
    [IsReduced A] [Algebra.FiniteType k A] (a : A) (h : ∀ e : A →ₐ[k] k, e a = 0) : a = 0 := by
  apply (config := { allowSynthFailures := true }) GlobalTheory.ZH.ConePrime.eq_zero_of_forall_algHom <;> assumption

theorem isReduced_complex_tensor (D : Type) [CommRing D] [IsDomain D] [Algebra ℚ D]
    [Algebra.FiniteType ℚ D] : IsReduced (ℂ ⊗[ℚ] D) := by
  set K := FractionRing D
  have : Algebra.EssFiniteType ℚ K := inferInstanceAs (Algebra.EssFiniteType ℚ (Localization _))
  have h1 : IsReduced (K ⊗[ℚ] ℂ) := ReciprocityTheory.AnForm.R.BaseChangeC.isReduced_tensor_of_essFiniteType K ℂ
  have h2 : IsReduced (ℂ ⊗[ℚ] K) :=
    isReduced_of_injective (Algebra.TensorProduct.comm ℚ ℂ K).toRingEquiv.toRingHom
      (Algebra.TensorProduct.comm ℚ ℂ K).injective
  have hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id ℚ ℂ)
      (IsScalarTower.toAlgHom ℚ D K)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective _ _)
  exact isReduced_of_injective (Algebra.TensorProduct.map (AlgHom.id ℚ ℂ)
      (IsScalarTower.toAlgHom ℚ D K)).toRingHom hinj

theorem exists_det_ne_zero (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Algebra.FiniteType ℤ B]
    (r : ℕ) (f : Fin r → B) (hf : LinearIndependent ℤ f) :
    ∃ x : Fin r → (B →+* ℂ), (Matrix.of fun i j => x i (f j)).det ≠ 0 := by
  classical
  let K := FractionRing B
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra ℤ B).FG)
  let D : Subalgebra ℚ K := Algebra.adjoin ℚ ((algebraMap B K) '' (s : Set B))
  have hmem : ∀ b : B, algebraMap B K b ∈ D := by
    intro b
    have hb : b ∈ Algebra.adjoin ℤ (s : Set B) := by rw [hs]; trivial
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
    | algebraMap n => rw [eq_intCast, map_intCast]; exact intCast_mem D n
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  haveI : Algebra.FiniteType ℚ D := by
    rw [← Subalgebra.fg_iff_finiteType]
    have := Subalgebra.fg_adjoin_finset (R := ℚ) (s.image (algebraMap B K))
    simpa [D] using this
  let g : B →+* D := (algebraMap B K).codRestrict D hmem
  have hg : Function.Injective g := fun a b h =>
    IsFractionRing.injective B K (congrArg Subtype.val h)
  have hD : LinearIndependent ℚ (fun j => g (f j)) := by
    rw [← LinearIndependent.iff_fractionRing ℤ ℚ]
    exact hf.map' g.toAddMonoidHom.toIntLinearMap (LinearMap.ker_eq_bot.mpr hg)
  have hT : LinearIndependent ℂ (fun j => (1 : ℂ) ⊗ₜ[ℚ] g (f j)) :=
    Module.Flat.linearIndependent_one_tmul hD
  haveI : IsReduced (ℂ ⊗[ℚ] D) := isReduced_complex_tensor D
  let pt : ((ℂ ⊗[ℚ] D) →ₐ[ℂ] ℂ) → (B →+* ℂ) := fun φ =>
    (φ.toRingHom.comp (Algebra.TensorProduct.includeRight (R := ℚ) (A := ℂ) (B := D)).toRingHom).comp g
  let S : Set (Fin r → ℂ) := Set.range fun x : B →+* ℂ => fun j => x (f j)
  have hspan : Submodule.span ℂ S = ⊤ := by
    by_contra hne
    obtain ⟨ℓ, hℓ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    let c : Fin r → ℂ := fun i => ℓ (fun j => if i = j then 1 else 0)
    have hℓv : ∀ v, ℓ v = ∑ i, v i * c i := fun v => by
      rw [LinearMap.pi_apply_eq_sum_univ ℓ v]; rfl
    have hu : ∑ i, c i • ((1 : ℂ) ⊗ₜ[ℚ] g (f i)) = 0 := by
      apply eq_zero_of_forall_algHom (k := ℂ)
      intro φ
      have h0 : ℓ (fun j => pt φ (f j)) = 0 := hle (Submodule.subset_span ⟨pt φ, rfl⟩)
      rw [hℓv] at h0

      rw [map_sum, ← h0]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
      rfl
    have hc : c = 0 := funext fun i => Fintype.linearIndependent_iff.mp hT c hu i
    apply hℓ
    refine LinearMap.ext fun v => ?_
    rw [hℓv, hc]
    simp
  obtain ⟨b, hbS, hbspan, hli⟩ := exists_linearIndependent ℂ S
  have hb_top : ⊤ ≤ Submodule.span ℂ (Set.range ((↑) : b → Fin r → ℂ)) := by
    rw [Subtype.range_coe, hbspan, hspan]
  let bb := Module.Basis.mk hli hb_top
  let e : b ≃ Fin r := bb.indexEquiv (Pi.basisFun ℂ (Fin r))
  have hx : ∀ i : Fin r, ∃ x : B →+* ℂ, (fun j => x (f j)) = ((e.symm i : b) : Fin r → ℂ) :=
    fun i => hbS (e.symm i).2
  choose x hx using hx
  refine ⟨x, ?_⟩
  have hrows : LinearIndependent ℂ (fun i => (Matrix.of fun i j => x i (f j)) i) := by
    have : (fun i => (Matrix.of fun i j => x i (f j)) i) = (fun v : b => (v : Fin r → ℂ)) ∘ e.symm := by
      funext i; exact hx i
    rw [this]; exact hli.comp _ e.symm.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hrows)).ne_zero

end GlobalTheory.CxPointsSep
