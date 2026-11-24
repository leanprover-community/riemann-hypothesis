module

public import Development.AbelianVarietyTheory.Definitions.UpperBounds.SingleMemIntVec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsIntMulIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ComplexConjugate ComplexOrder Matrix

namespace GlobalTheory.Member.LatData

open GlobalTheory.Up.Definite GlobalTheory.LatFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

open NumberField in
open scoped ComplexConjugate ComplexOrder Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [IsCMField E] in
private theorem exists_int_smul_single_mem_of_span_eq_univ (Λ : Submodule (𝓞 E) (Fin r → E))
    (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) :
    ∃ c : ℤ, c ≠ 0 ∧ ∀ b : Fin r, (c : E) • (Pi.single b 1 : Fin r → E) ∈ Λ := by
  classical
  have hmem : ∀ b : Fin r, (Pi.single b 1 : Fin r → E) ∈ Submodule.span E (Λ : Set (Fin r → E)) :=
    fun b => hspan ▸ Submodule.mem_top
  choose f t ht _ hsum using fun b => Submodule.mem_span_iff_exists_finset_subset.1 (hmem b)
  obtain ⟨c, hc, hcint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.biUnion fun b => (t b).image (f b))
  refine ⟨c, hc, fun b => ?_⟩
  have key : ∀ v ∈ t b, (c : E) • (f b v • v) ∈ Λ := by
    intro v hv
    have hI : IsIntegral ℤ ((c : E) * f b v) := by
      have h := hcint (f b v) (Finset.mem_biUnion.2 ⟨b, Finset.mem_univ _, Finset.mem_image_of_mem _ hv⟩)
      rwa [zsmul_eq_mul] at h
    have h : (c : E) • (f b v • v) = (⟨_, hI⟩ : 𝓞 E) • v := by
      rw [smul_smul]
      rfl
    rw [h]
    exact Λ.smul_mem _ (ht b hv)
  rw [← hsum b, Finset.smul_sum]
  exact Λ.sum_mem key

open NumberField in
open scoped ComplexConjugate ComplexOrder Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private theorem cc_intCast' (n : ℤ) : _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (n : E) = n := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply φ.injective
  rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.emb_cc, map_intCast, map_intCast]

open NumberField in
open scoped ComplexConjugate ComplexOrder Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [IsCMField E] in
private theorem finite_GL_of_integral_bounded_scaled_entries (c : E) (hc : c ≠ 0) (B : ℝ) :
    {γ : GL (Fin r) E | ∀ a b, IsIntegral ℤ (c * (γ : Matrix (Fin r) (Fin r) E) a b) ∧
      ∀ φ : E →+* ℂ, ‖φ (c * (γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ B}.Finite := by
  have hT := Embeddings.finite_of_norm_le E ℂ B
  have hpi : (Set.univ.pi fun _ : Fin r => Set.univ.pi fun _ : Fin r =>
      {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ B}).Finite :=
    Set.Finite.pi fun _ => Set.Finite.pi fun _ => hT
  have hinj : Function.Injective fun γ : GL (Fin r) E => fun a b => c * (γ : Matrix (Fin r) (Fin r) E) a b := by
    intro γ δ h
    ext a b
    exact mul_left_cancel₀ hc (congrFun (congrFun h a) b)
  refine (hpi.preimage hinj.injOn).subset fun γ hγ => ?_
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf_eq]
  exact fun a b => hγ a b


open NumberField in
open scoped ComplexConjugate ComplexOrder Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.Member.LatData.exists_data_lattice : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (r : ℕ)
    (Λ : Submodule (𝓞 E) (Fin r → E)), Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ →
    ∃ X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r, X.Λ = Λ := by
  intro E _ _ _ r Λ hfg hspan
  obtain ⟨d, hd, hdint⟩ := _root_.GlobalTheory.LatFin.exists_common_den Λ hfg
  obtain ⟨c, hc, hcmem⟩ := exists_int_smul_single_mem_of_span_eq_univ Λ hspan
  have hdc : ((d * c : ℤ) : E) ≠ 0 := by exact_mod_cast mul_ne_zero hd hc
  refine ⟨{ _root_.GlobalTheory.Up.Definite.data (E := E) (r := r) with
    Λ := Λ
    Λ_fg := hfg
    Λ_span := hspan
    den := (d : 𝓞 E) * (d : 𝓞 E)
    den_ne := by exact_mod_cast mul_ne_zero hd hd
    Λ_int := ?_
    Γ_stab := ?_
    Γ_index := ?_
    transv := by
      intro ξ _ hiso s _ _
      change _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (1 : Matrix (Fin r) (Fin r) E) ξ ξ = 0 at hiso
      obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
      have h1 := congrArg φ hiso
      rw [_root_.GlobalTheory.Up.Definite.map_herm_one_self, map_zero, Complex.ofReal_eq_zero,
        Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _] at h1
      have hξ : ∀ a, ξ a = 0 := fun a => by simpa using h1 a (Finset.mem_univ a)
      refine ⟨1, Subgroup.one_mem _, ?_⟩
      ext a b
      simp [_root_.GlobalTheory.Up.Definite.data, _root_.ReciprocityTheory.ChartRestriction.G.FD.transvMat, hξ, Matrix.one_apply] }, rfl⟩
  · intro x hx y hy
    show IsIntegral ℤ ((((d : 𝓞 E) * (d : 𝓞 E) : 𝓞 E) : E) * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (1 : Matrix (Fin r) (Fin r) E) x y)
    rw [_root_.GlobalTheory.Up.Definite.herm_one, Finset.mul_sum]
    refine IsIntegral.sum _ fun a _ => ?_
    have h : (((d : 𝓞 E) * (d : 𝓞 E) : 𝓞 E) : E) * (x a * _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (y a)) =
        ((d : E) * x a) * _root_.ReciprocityTheory.ChartRestriction.G.FD.cc ((d : E) * y a) := by
      rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.cc_mul, cc_intCast',
        show (((d : 𝓞 E) * (d : 𝓞 E) : 𝓞 E) : E) = (d : E) * (d : E) by simp]
      ring
    rw [h]
    exact (hdint x hx a).mul (_root_.ReciprocityTheory.ChartRestriction.G.FD.isIntegral_cc (hdint y hy a))
  · intro γ hγ
    change γ ∈ (⊥ : Subgroup (GL (Fin r) E)) at hγ
    rw [Subgroup.mem_bot] at hγ
    subst hγ
    simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab]
  · refine ⟨(finite_GL_of_integral_bounded_scaled_entries ((d * c : ℤ) : E) hdc ‖((d * c : ℤ) : ℂ)‖).toFinset,
      fun γ hγ => ⟨γ, ?_, by simp⟩⟩
    rw [Set.Finite.mem_toFinset]
    intro a b
    have hcol : (γ : Matrix (Fin r) (Fin r) E) *ᵥ (Pi.single b 1) =
        fun a => (γ : Matrix (Fin r) (Fin r) E) a b := by
      ext a; simp
    have hnorm : ∀ φ : E →+* ℂ, ‖φ ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ 1 := by
      intro φ
      have h0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (1 : Matrix (Fin r) (Fin r) E) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ Pi.single b 1)
          ((γ : Matrix (Fin r) (Fin r) E) *ᵥ Pi.single b 1) =
          _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (1 : Matrix (Fin r) (Fin r) E) (Pi.single b 1) (Pi.single b 1) := hγ.1 _ _
      have h1 := congrArg φ h0
      rw [_root_.GlobalTheory.Up.Definite.map_herm_one_self, _root_.GlobalTheory.Up.Definite.map_herm_one_self, hcol] at h1
      have h2 : ∑ a, ‖φ ((Pi.single b 1 : Fin r → E) a)‖ ^ 2 = 1 := by
        rw [Finset.sum_eq_single b] <;> simp +contextual
      have h3 := Complex.ofReal_injective h1
      rw [h2] at h3
      have h4 := Finset.single_le_sum (f := fun a => ‖φ ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ a)
      rw [h3] at h4
      nlinarith [norm_nonneg (φ ((γ : Matrix (Fin r) (Fin r) E) a b))]
    refine ⟨?_, fun φ => ?_⟩
    · have hmemγ := (hγ.2 _).mp (hcmem b)
      have hi := hdint _ hmemγ a
      rw [Matrix.mulVec_smul, hcol] at hi
      simp only [Pi.smul_apply, smul_eq_mul] at hi
      have h : ((d * c : ℤ) : E) * (γ : Matrix (Fin r) (Fin r) E) a b =
          (d : E) * ((c : E) * (γ : Matrix (Fin r) (Fin r) E) a b) := by
        push_cast
        ring
      rw [h]
      exact hi
    · rw [map_mul, norm_mul, map_intCast]
      exact mul_le_of_le_one_right (norm_nonneg _) (hnorm φ)

end GlobalTheory.Member.LatData
