import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThEqClassicalThetaFunctionValues
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusProjPeriodZeroEqReal
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumLocallyUniformlyOnTerm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormalThetaSumShiftPeriodDiv
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AnalyticDictionaryIsPointPeriodOrigin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TxStOfPtSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNumOf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.StalkUnitsSymmGm
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DifferentiableQuot
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralDegenerationValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CmFieldHostElementAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLogFrame
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.QvalAddTower
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceEqFinrankMulSum
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TwoMulEqOfIsTypeFn
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsOfDouble
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetCondOfEigenbasis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueSumSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLieBasisOfHolUnif
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LambdaBundleAdjointOfWeilPairingAdjoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPointOfIsPeriod
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyUniformisationFibreTheta
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLatticeUniformisationOfPrimTheta
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPairingValuesOfFamiliesValues

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

namespace GlobalTheory.Ex.Arch

theorem period_constantPart_eq_zero_injective {O : Type} [CommRing O] [StarRing O] (B : AnArc O) (la : B.La) (hy : la.y = 0)
    (h : B.P0 la = 0) : la = 0 := by
  have hl : la.l = 0 := by
    have := congrArg Prod.snd h
    rw [AnArc.degeneratingTori_basePeriodMap_snd, hy, map_zero, zero_add] at this
    exact Subtype.ext this
  refine AnArc.La.ext hy (AddMonoidHom.ext fun x => ?_) hl
  have : (B.P0 la).1 x = 0 := by rw [h]; rfl
  rw [AnArc.degeneratingTori_basePeriodMap_fst_apply, hy, hl] at this
  simpa using this

theorem qkSt_of_ptSt : PtSt → QkSt := by
  intro hP O _ _ N B d k hk
  obtain ⟨h1, h2, h3, h4, h5⟩ := hP O N B d
  choose E hE hU using h1
  have hiff : ∀ v g, d.IsPt v g ↔ g = E v := fun v g => ⟨hU v g, fun h => h ▸ hE v⟩
  have hadd : ∀ v v', E (v + v') = E v * E v' := fun v v' => (hU _ _ (h3 _ _ _ _ (hE v) (hE v'))).symm
  have hzero : E 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hpow : ∀ (n : ℕ) v, E (n • v) = E v ^ n := fun n v => by
    induction n with
    | zero => rw [zero_nsmul, pow_zero, hzero]
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have hper : ∀ la : B.La, E (B.P0 la) = N.io (d.eX la.y) := fun la => (hU _ _ (h5 la)).symm
  have hker : ∀ v v', E v = E v' → ∃ la : B.La, la.y = 0 ∧ v = v' + B.P0 la := fun v v' h => by
    have e : E (v - v') * E v' = E v' := by rw [← hadd, sub_add_cancel, h]
    obtain ⟨la, hy, hl⟩ := (h4 (v - v')).1 ((hiff _ _).2 (mul_eq_right.1 e).symm)
    exact ⟨la, hy, by rw [← hl, add_sub_cancel]⟩
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hc1 : ∀ v : B.V, (k : ℂ)⁻¹ • (k • v) = v := fun v => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ hk0]
  have hc2 : ∀ v : B.V, k • ((k : ℂ)⁻¹ • v) = v := fun v => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ hk0]
  have hrep : ∀ (la : B.La) (p : N.QT k), d.Rep k la p ↔
      p.1.1.toAdd = d.eX la.y ∧ p.1.2 = E ((k : ℂ)⁻¹ • B.P0 la) := fun la p => and_congr Iff.rfl (hiff _ _)
  refine ⟨fun p => ?_, fun la => ?_, fun la la' p p' h h' => ?_, fun la la' p p' h h' => ?_⟩
  · obtain ⟨v, hv⟩ := h2 p.1.2
    have hv' := (hiff _ _).1 hv
    have e : E (k • v) = E (B.P0 (AnArc.La.mk (d.eX.symm p.1.1.toAdd) 0 0)) := by
      rw [hpow, hper, ← hv', AnArc.La.mk_y, AddEquiv.apply_symm_apply]
      exact N.mem_QT.1 p.2
    obtain ⟨la, hy, hl⟩ := hker _ _ e
    refine ⟨AnArc.La.mk (d.eX.symm p.1.1.toAdd) 0 0 + la, (hrep _ _).2 ⟨?_, ?_⟩⟩
    · rw [AnArc.La.add_y, hy, add_zero, AnArc.La.mk_y, AddEquiv.apply_symm_apply]
    · rw [map_add, ← hl, hc1, hv']
  · refine ⟨⟨(Multiplicative.ofAdd (d.eX la.y), E ((k : ℂ)⁻¹ • B.P0 la)), ?_⟩, (hrep _ _).2 ⟨rfl, rfl⟩, fun p hp => ?_⟩
    · rw [NumD.mem_QT, ← hpow, hc2, hper]
      rfl
    · obtain ⟨a, b⟩ := (hrep _ _).1 hp
      exact Subtype.ext (Prod.ext a b)
  · obtain ⟨a, b⟩ := (hrep _ _).1 h
    obtain ⟨a', b'⟩ := (hrep _ _).1 h'
    refine (hrep _ _).2 ⟨?_, ?_⟩
    · rw [AnArc.La.add_y, map_add, ← a, ← a']
      rfl
    · rw [map_add, smul_add, hadd, ← b, ← b']
      rfl
  · obtain ⟨a, b⟩ := (hrep _ _).1 h
    obtain ⟨a', b'⟩ := (hrep _ _).1 h'
    constructor
    · rintro ⟨z, c, c'⟩
      set z₀ : B.La := AnArc.La.mk (d.eX.symm z) 0 0 with hz₀
      have hz : d.eX z₀.y = z := by rw [hz₀, AnArc.La.mk_y, AddEquiv.apply_symm_apply]
      have e : E ((k : ℂ)⁻¹ • B.P0 la') = E ((k : ℂ)⁻¹ • B.P0 la + B.P0 z₀) := by
        rw [hadd, hper, hz, ← b, ← b', c']
      obtain ⟨e₀, hy, hl⟩ := hker _ _ e
      refine ⟨z₀ + e₀, sub_eq_zero.1 (period_constantPart_eq_zero_injective B _ ?_ ?_)⟩
      · apply d.eX.injective
        rw [AnArc.La.sub_y, AnArc.La.add_y, AnArc.La.nsmul_y, AnArc.La.add_y, hy, add_zero, map_sub, map_add,
          map_nsmul, hz, ← a, ← a', c, sub_self, map_zero]
      · rw [map_sub, map_add, map_nsmul, map_add, ← hc2 (B.P0 la'), hl, add_assoc, smul_add, hc2, sub_self]
    · rintro ⟨e, rfl⟩
      refine ⟨d.eX e.y, ?_, ?_⟩
      · rw [a, a', AnArc.La.add_y, AnArc.La.nsmul_y, map_add, map_nsmul]
      · rw [b, b', map_add, map_nsmul, smul_add, hc1, hadd, hper]

end GlobalTheory.Ex.Arch
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch
noncomputable section
namespace GlobalTheory.Ex.Arch.Wp

variable {O : Type} [CommRing O] [StarRing O] {N : NumD ℂ} {B : AnArc O}

theorem ex_nsmul (d : Dict N B) (i : ℕ) (z : Fin B.gB → ℂ) : d.ex (i • z) = d.ex z ^ i := by
  induction i with
  | zero =>
    rw [zero_smul, pow_zero]
    exact (d.ab.2.2.1 0).2 (zero_mem _)
  | succ i ih => rw [succ_nsmul, d.ab.1, ih, pow_succ]

theorem cubN_frame (d : Dict N B) (k : ℕ) (x' x : Fin B.gB → ℂ) :
    cubN N.θ k 1 (d.ex x') (d.ex x) * d.fr (k • x') * d.fr x * d.fr (x' + x) ^ k =
      d.fr (k • x' + x) * (d.fr x' * d.fr x) ^ k := by
  induction k with
  | zero => simp [cubN, d.ab.2.2.2.1]
  | succ k ih =>
    have h := d.ab.2.2.2.2.2.1 (k • x') x' x
    rw [ex_nsmul] at h
    rw [cubN] at ih
    rw [cubN, Finset.prod_range_succ, succ_nsmul, _root_.one_mul (d.ex x' ^ k)]
    replace h := congrArg Additive.ofMul h
    replace ih := congrArg Additive.ofMul ih
    apply Additive.ofMul.injective
    simp only [pow_succ, ofMul_mul] at h ih ⊢
    linear_combination (norm := abel) h + ih

theorem tk_frame (d : Dict N B) {k : ℕ} (hk : 0 < k) {la la' : B.La} {p p' : N.QT k} (h : d.Rep k la p)
    (h' : d.Rep k la' p') :
    (N.tk p p' : ℂ) * (d.fr (((k : ℂ)⁻¹ • B.P0 la').2 + ((k : ℂ)⁻¹ • B.P0 la).2) : ℂ) ^ k =
      Complex.exp (2 * Real.pi * Complex.I * ((k : ℂ)⁻¹ • B.P0 la).1 la'.y -
          Real.pi * B.H ((k : ℂ)⁻¹ • B.P0 la).2 la'.l) *
        ((d.fr ((k : ℂ)⁻¹ • B.P0 la').2 : ℂ) * d.fr ((k : ℂ)⁻¹ • B.P0 la).2) ^ k := by
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  set x := ((k : ℂ)⁻¹ • B.P0 la).2 with hx
  set x' := ((k : ℂ)⁻¹ • B.P0 la').2 with hx'
  have e : k • x' = B.ct la'.y + la'.l := by
    rw [hx', Prod.smul_snd, AnArc.degeneratingTori_basePeriodMap_snd, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hk', one_smul]
  have c := congrArg (Units.val : ℂˣ → ℂ) (cubN_frame d k x' x)
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at c
  have s := h.2.2 la'.y
  have f1 := d.ab.2.2.2.2.1 la'.l (B.ct la'.y + x)
  have f2 := d.ab.2.2.2.2.1 la'.l (B.ct la'.y)
  rw [AnArc.ah_add, add_right_comm, ← e] at f1
  rw [← e] at f2
  rw [← hx, f1, f2, eTwoPi] at s
  rw [NumD.tk, h'.1, h.2.1, h'.2.1, Units.val_mul, Complex.exp_sub, ← hx, ← hx']
  have n1 := B.ah_ne_zero la'.l (B.ct la'.y)
  have n2 := (d.fr (k • x')).ne_zero
  have n3 := (d.fr x).ne_zero
  have n4 := (d.fr (k • x' + x)).ne_zero
  have n5 := Complex.exp_ne_zero (Real.pi * B.H x la'.l)
  rw [div_mul_eq_mul_div, eq_div_iff n5]
  apply mul_left_cancel₀ (mul_ne_zero n1 (mul_ne_zero n2 (mul_ne_zero n3 n4)))
  linear_combination (B.ah la'.l (B.ct la'.y) * Complex.exp (Real.pi * B.H x la'.l) * (d.fr (k • x' + x) : ℂ) *
    (p.1.2.s (d.eX la'.y) : ℂ)) * c + (((d.fr x' : ℂ) * d.fr x) ^ k * (d.fr (k • x' + x) : ℂ)) * s

theorem wp_eq : WpSt := by
  intro O _ _ N B d k hk la la' p p' h h'
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have a := tk_frame d hk h h'
  have b := tk_frame d hk h' h
  rw [add_comm, mul_comm (d.fr _ : ℂ)] at b
  have n1 := pow_ne_zero k (d.fr (((k : ℂ)⁻¹ • B.P0 la').2 + ((k : ℂ)⁻¹ • B.P0 la).2)).ne_zero
  have E : (B.Ef la.l la'.l : ℂ) = ((B.H la.l la'.l).im : ℂ) := by
    rw [← B.Ef_eq_im]; simp
  have C := Complex.sub_conj (B.H la.l la'.l)
  rw [B.H_conj] at C
  have key : Complex.exp (2 * Real.pi * Complex.I * ((k : ℂ)⁻¹ • B.P0 la).1 la'.y -
          Real.pi * B.H ((k : ℂ)⁻¹ • B.P0 la).2 la'.l) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (B.EF la la' : ℂ) / k) *
      Complex.exp (2 * Real.pi * Complex.I * ((k : ℂ)⁻¹ • B.P0 la').1 la.y -
          Real.pi * B.H ((k : ℂ)⁻¹ • B.P0 la').2 la.l) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [Prod.smul_fst, Prod.smul_snd, AddMonoidHom.smul_apply, AnArc.degeneratingTori_basePeriodMap_fst_apply, AnArc.degeneratingTori_basePeriodMap_snd,
      AnArc.H_smul_left, AnArc.H_add_left, smul_eq_mul, AnArc.EF_apply, B.T_symm la'.y la.y]
    push_cast at C ⊢
    rw [E]
    have hI := Complex.I_ne_zero
    field_simp
    linear_combination (-1 : ℂ) * C
  rw [NumD.wp, Units.val_div_eq_div_val, div_eq_iff (N.tk p' p).ne_zero]
  apply mul_right_cancel₀ n1
  rw [a, key, _root_.mul_assoc _ (N.tk p' p : ℂ), b, _root_.mul_assoc]

end GlobalTheory.Ex.Arch.Wp
end
end

section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
noncomputable section
namespace GlobalTheory.Ex.Arch

theorem exists_symm_bilin_ext {L V : Type} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L] [AddCommGroup V]
    [Module ℝ V] [Module ℂ V] [IsScalarTower ℝ ℂ V] (P : L →+ V) (hP : Submodule.span ℝ (Set.range P) = ⊤)
    (hr : Module.finrank ℤ L = Module.finrank ℝ V) (b : L →+ (V →ₗ[ℂ] ℂ)) (hb : ∀ a c, b a (P c) = b c (P a)) :
    ∃ Bs : V →ₗ[ℂ] V →ₗ[ℂ] ℂ, (∀ u v, Bs u v = Bs v u) ∧ ∀ a v, Bs (P a) v = b a v := by
  classical
  let e := Module.Free.chooseBasis ℤ L
  have htop : ⊤ ≤ Submodule.span ℝ (Set.range fun i => P (e i)) := by
    rw [← hP, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rw [← e.sum_repr a, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_zsmul]
    exact zsmul_mem (Submodule.subset_span (Set.mem_range_self (f := fun i => P (e i)) i)) _
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = Module.finrank ℝ V := by
    rw [← hr, Module.finrank_eq_card_chooseBasisIndex]
  let β := basisOfTopLeSpanOfCardEqFinrank _ htop hcard
  have hβ : ∀ i, β i = P (e i) := fun i => by simp [β]
  let f : V →ₗ[ℝ] (V →ₗ[ℂ] ℂ) := β.constr ℝ fun i => b (e i)
  have hf : ∀ a, f (P a) = b a := fun a => by
    rw [← e.sum_repr a]
    simp only [map_sum, map_zsmul, ← hβ, f, Module.Basis.constr_basis]
  have hs : ∀ u v, f u v = f v u := by
    let F : V →ₗ[ℝ] V →ₗ[ℝ] ℂ := LinearMap.mk₂ ℝ (fun u v => f u v) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
      (fun _ _ _ => by simp) (fun _ _ _ => by simp)
    have : F = F.flip := β.ext fun i => β.ext fun j => by
      change f (β i) (β j) = f (β j) (β i)
      rw [hβ, hβ, hf, hf, hb]
    exact fun u v => LinearMap.congr_fun₂ this u v
  refine ⟨LinearMap.mk₂ ℂ (fun u v => f u v) (fun _ _ _ => by simp) (fun c u v => ?_) (fun _ _ _ => by simp)
    (fun _ _ _ => by simp), hs, fun a v => ?_⟩
  · rw [hs, map_smul, hs]
  · exact congrArg (fun g => g v) (hf a)

theorem hermForm_sub_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    hermForm Hm z w - hermForm Hm w z = 2 * Complex.I * (hermForm Hm z w).im := by
  have h : ∀ i k, starRingEnd ℂ (Hm i k) = Hm k i := fun i k => hH.apply k i
  have hc : starRingEnd ℂ (hermForm Hm z w) = hermForm Hm w z := by
    simp only [hermForm, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, h, Pi.star_apply,
      RCLike.star_def, Complex.conj_conj]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  rw [← hc, Complex.sub_conj]
  push_cast; ring

variable {O : Type} [CommRing O] [StarRing O] (B : AnArc O)

theorem lin_period (w : ℂ) (a c : B.La) : lin B a (B.Pw w c) =
    -(2 * Real.pi * Complex.I) * (B.T c.y a.y + c.n a.y + w * B.be c.y a.y) +
      Real.pi * (B.H (B.ct a.y) c.l + B.H (B.ct c.y) a.l + B.H c.l a.l) := by
  have := Complex.I_ne_zero
  rw [lin, AnArc.Pw_fst_apply, AnArc.Pw_snd, AnArc.H_add_left]
  field_simp
  ring

theorem lin_period_sub (w : ℂ) (a c : B.La) :
    lin B a (B.Pw w c) - lin B c (B.Pw w a) = -(2 * Real.pi * Complex.I) * B.EF a c := by
  have h := hermForm_sub_swap B.Hm_herm a.l c.l
  rw [← B.Ef_eq, ← B.H_def, ← B.H_def] at h
  rw [lin_period, lin_period, B.T_symm c.y, B.be_symm c.y, AnArc.EF_apply]
  push_cast at h ⊢
  linear_combination (-Real.pi : ℂ) * h

theorem perFactor_of_isPrim {w₀ : O} (hp : IsPrim B w₀) (w : ℂ) (a : B.La) (v : B.V) :
    B.perFactor w a v = (-1) ^ B.EF a (w₀ • a) * Complex.exp (lin B a v + lin B a (B.Pw w a) / 2) := by
  obtain ⟨h1, h2, h3⟩ := hp
  have hy : w₀ • a.y + star w₀ • a.y = a.y := by rw [← add_smul, h1, one_smul]
  have hT : B.T a.y a.y = 2 * B.T a.y (w₀ • a.y) := by
    have := congrArg (B.T a.y) hy
    rw [map_add, ← B.T_adj, B.T_symm (w₀ • a.y)] at this
    rw [← this]; ring
  have hE : B.EF a (w₀ • a) = B.Ef a.l (B.FLam w₀ a.l) + (a.n a.y + 2 * (-a.n (w₀ • a.y))) := by
    have := congrArg a.n hy
    rw [map_add] at this
    rw [AnArc.EF_apply, AnArc.La.smul_n_apply, AnArc.La.smul_y, AnArc.La.smul_l]
    omega
  have hq : (B.be a.y a.y : ℂ) = 2 * B.q a.y := by rw [← B.two_mul_q]; push_cast; ring
  have hs : ((-1 : ℂ)) ^ (a.n a.y + 2 * (-a.n (w₀ • a.y))) = Complex.exp (Real.pi * Complex.I * a.n a.y) := by
    rw [zpow_add₀ (by norm_num), zpow_mul, mul_comm _ (a.n a.y : ℂ), Complex.exp_int_mul, Complex.exp_pi_mul_I]
    norm_num
  rw [hE, zpow_add₀ (by norm_num), hs, AnArc.perFactor, AnArc.ah, h2, h3, lin_period, hT, hq, lin, AnArc.H_add_left,
    ← AnArc.e_add, ← AnArc.e_add, eTwoPi, ← Complex.exp_neg, mul_assoc (_ ^ _), mul_assoc (_ ^ _), ← Complex.exp_add,
    ← Complex.exp_add]
  congr 2
  ring

theorem theta_sum_appellHumbert : ThetaSt := by
  intro O _ _ B w₀ hp th hth w hS g h Hm hH hsp hE
  let b : B.La →+ (B.V →ₗ[ℂ] ℂ) := AddMonoidHom.mk' (fun a =>
    { toFun := fun v => lin B a v - Real.pi * hermForm Hm (h v) (h (B.Pw w a))
      map_add' := fun v v' => by
        simp only [lin, hermForm, map_add, add_dotProduct, Prod.fst_add, Prod.snd_add, AddMonoidHom.add_apply,
          AnArc.H_add_left]
        ring
      map_smul' := fun c v => by
        simp only [lin, hermForm, map_smul, smul_dotProduct, Prod.smul_fst, Prod.smul_snd, AddMonoidHom.smul_apply,
          AnArc.H_smul_left, smul_eq_mul, RingHom.id_apply]
        ring }) fun a a' => LinearMap.ext fun v => by
      simp only [lin, hermForm, map_add, star_add, Matrix.mulVec_add, dotProduct_add, AnArc.La.add_y, AnArc.La.add_l,
        Submodule.coe_add, AnArc.H_add_right, LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
      ring
  have hb : ∀ a v, b a v = lin B a v - Real.pi * hermForm Hm (h v) (h (B.Pw w a)) := fun _ _ => rfl
  obtain ⟨Bs, hs, hB⟩ := exists_symm_bilin_ext (B.Pw w) hsp B.finrank_La b fun a c => by
    have h1 := hermForm_sub_swap hH (h (B.Pw w a)) (h (B.Pw w c))
    rw [hE] at h1
    push_cast at h1
    rw [hb, hb]
    linear_combination lin_period_sub B w a c + (Real.pi : ℂ) * h1
  refine ⟨fun z => Complex.exp (-(Bs (h.symm z) (h.symm z) / 2)) * B.Sum 1 0 th w (h.symm z), ?_, fun v => ?_,
    fun a z => ?_, fun a m hm => ?_⟩
  · have hd : Differentiable ℂ fun z => h.symm z := h.symm.toContinuousLinearEquiv.differentiable
    let Bc : B.V →L[ℂ] B.V →L[ℂ] ℂ :=
      LinearMap.toContinuousLinearMap ((LinearMap.toContinuousLinearMap : (B.V →ₗ[ℂ] ℂ) ≃ₗ[ℂ] _).toLinearMap ∘ₗ Bs)
    have hq : Differentiable ℂ fun v : B.V => Bs v v := Bc.differentiable.clm_apply differentiable_id
    have hq' : Differentiable ℂ fun z => Bs (h.symm z) (h.symm z) := hq.comp hd
    have hq'' : Differentiable ℂ fun z => -(Bs (h.symm z) (h.symm z) / 2) := by
      simp only [div_eq_mul_inv]
      exact (hq'.mul_const _).neg
    exact hq''.cexp.mul (hS.comp hd)
  · simp only [h.symm_apply_apply, mul_eq_zero, Complex.exp_ne_zero, false_or]
  · obtain ⟨v, rfl⟩ := h.surjective z
    simp only [← map_add, h.symm_apply_apply]
    rw [B.Sum_add_period hth, pow_one, perFactor_of_isPrim B hp]
    simp only [map_add, LinearMap.add_apply, hs v (B.Pw w a), hB, hb]
    have e : ∀ s x y x' y' S : ℂ, x + y = x' + y' →
        Complex.exp x * (s * Complex.exp y * S) = s * Complex.exp x' * (Complex.exp y' * S) := fun s x y x' y' S e => by
      have := congrArg Complex.exp e
      rw [Complex.exp_add, Complex.exp_add] at this
      linear_combination s * S * this
    exact e _ _ _ _ _ _ (by ring)
  · have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm
    simp only [← map_smul, h.symm_apply_apply]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hB, hb]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    field_simp
    ring

end GlobalTheory.Ex.Arch
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section
namespace GlobalTheory.Ex.Arch.FibEx
open GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter GlobalTheory.EigenNorm GlobalTheory.FrameValue

theorem val_iso {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {L M : LB X} (hM : M.IsLB) {w : LB.Iso L M} (hw : w.IsGen)
    (m : M.ι) (i j : L.ι) (hm : ⊤ ≤ x ⁻¹ᵁ M.U m) (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) :
    valAt' x _ (w.s (m, i)).val * valAt' x (L.U i ⊓ L.U j) (L.g i j).val = valAt' x _ (w.s (m, j)).val := by
  have h : ⊤ ≤ x ⁻¹ᵁ (M.U m ⊓ L.U i ⊓ (M.U m ⊓ L.U j)) :=
    (le_preimage_inf x _ _).2 ⟨(le_preimage_inf x _ _).2 ⟨hm, hi⟩, (le_preimage_inf x _ _).2 ⟨hm, hj⟩⟩
  have l₁ : M.U m ⊓ L.U i ⊓ (M.U m ⊓ L.U j) ≤ M.U m ⊓ M.U m :=
    le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  have l₂ : M.U m ⊓ L.U i ⊓ (M.U m ⊓ L.U j) ≤ L.U i ⊓ L.U j :=
    le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  suffices H : ∀ (a : Γ(X, M.U m ⊓ L.U i)ˣ) (b : Γ(X, M.U m ⊓ L.U j)ˣ), res inf_le_left a =
      res l₁ (M.g m m) * (res l₂ (L.g i j))⁻¹ * res inf_le_right b →
      valAt' x _ a.val * valAt' x (L.U i ⊓ L.U j) (L.g i j).val = valAt' x _ b.val from
    H (w.s (m, i)) (w.s (m, j)) (hw (m, i) (m, j))
  intro a b e
  have e' : res inf_le_left a * res l₂ (L.g i j) = res l₁ (M.g m m) * res inf_le_right b := by
    rw [e, mul_right_comm, inv_mul_cancel_right]
  have o : valAt' x (M.U m ⊓ M.U m) (M.g m m).val = 1 := by
    obtain ⟨ev, hev⟩ := (valueRules X x).2.1 _ hm
    rw [← val_res x valueRules (le_inf le_rfl le_rfl) hm, hM.g_self, hev, Units.val_one, map_one]
  have v := congrArg (fun q : Γ(X, _)ˣ => valAt' x _ q.val) e'
  obtain ⟨ev, hev⟩ := (valueRules X x).2.1 _ h
  simp only [hev, Units.val_mul, map_mul] at v
  simp only [← hev] at v
  rw [val_res x valueRules _ h, val_res x valueRules _ h, val_res x valueRules _ h, val_res x valueRules _ h, o,
    _root_.one_mul] at v
  exact v

theorem fibEx : Laws → ThetaUnifAV → FibExSt := by
  intro hL hT R _ _ _ P J hJ
  obtain ⟨P', φ, hφ, -, hmul, t, ht⟩ := hL.polBaseChange _ _ (TF (R := R) ℂ).hom P
  have gp : IsGrpPullback P'.A P.A (TF (R := R) ℂ).hom φ := ⟨hφ, fun T x y x₀ y₀ hx hy => by
    have ex : x₀ = toBase hφ.w x := Over.OverMorphism.ext hx
    have ey : y₀ = toBase hφ.w y := Over.OverMorphism.ext hy
    rw [ex, ey, ← hmul]; rfl⟩
  obtain ⟨w, hw⟩ := LBIso.symm ⟨t, ht⟩
  obtain ⟨rig, hrig⟩ := P'.rigid
  obtain ⟨u, Hm, χ, Ef, hAH, -, h₁, h₂, h₃, -, hE, hB, -⟩ := hT P' rig hrig
  let ex : (Fin P'.g → ℂ) → (TF (R := R) ℂ ⟶ P.A) := fun z => Over.homMk ((u.ex z).left ≫ φ) (by
    show ((u.ex z).left ≫ φ) ≫ P.A.hom = _
    rw [Category.assoc, hφ.w, ← Category.assoc, Over.w]
    exact Category.id_comp _)
  have hm : ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (P.L.pull φ).U (fun _ => J (ex z).left) := fun z =>
    (le_preimage_wchart _ P.L _ _).2 fun _ => hJ _
  have hc := fun z => le_chartAt P'.isLB (u.ex z).left
  refine ⟨P'.g, u.Λ, Hm, χ, Ef, ex, fun z => Units.mk0
    (valAt' (u.ex z).left _ (w.s (fun _ => J (ex z).left, chartAt P'.isLB (u.ex z).left)).val *
      u.fr (chartAt P'.isLB (u.ex z).left) z)
    (mul_ne_zero (val_unit_ne_zero _ valueRules ((le_preimage_inf _ _ _).2 ⟨hm z, hc z⟩) _) (u.fr_ne _ _ (hc z))),
    ⟨hJ, P', φ, w, u, rfl, gp, hw, hAH, h₁, h₂, h₃, fun _ => rfl, fun z i hi => ?_⟩, hE, hB⟩
  rw [Units.val_mk0, u.fr_compat _ i z ((le_preimage_inf _ _ _).2 ⟨hc z, hi⟩), ← _root_.mul_assoc]
  exact congrArg (· * u.fr i z) (val_iso _ (pull_isLB P.isLB φ) hw _ _ _ (hm z) (hc z) hi)

end GlobalTheory.Ex.Arch.FibEx
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section

namespace GlobalTheory.Ex.Arch

theorem exists_pull_endo {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {b : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (hg : IsGrpPullback G' G b φ) (f : G ⟶ G) (hf : IsMonHom f) :
    ∃ f' : G' ⟶ G', IsMonHom f' ∧ f'.left ≫ φ = φ ≫ f.left := by
  have inj : ∀ {T : Over S'} {x y : T ⟶ G'}, pushPt hg.1.w x = pushPt hg.1.w y → x = y := fun {T x y} h =>
    Over.OverMorphism.ext (hg.1.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))
  let f' : G' ⟶ G' := Over.homMk (hg.1.lift (φ ≫ f.left) G'.hom
    (by rw [Category.assoc, Over.w, hg.1.w])) (hg.1.lift_snd _ _ _)
  have ha : f'.left ≫ φ = φ ≫ f.left := hg.1.lift_fst _ _ _
  have pa : ∀ {T : Over S'} (x : T ⟶ G'), pushPt hg.1.w (x ≫ f') = pushPt hg.1.w x ≫ f := fun x =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, ha, Category.assoc])
  have pm : ∀ {T : Over S'} (x y : T ⟶ G'), pushPt hg.1.w (x * y) = pushPt hg.1.w x * pushPt hg.1.w y := fun x y =>
    map_mul (pushHom hg _) x y
  refine ⟨f', isMonHom_of_mul _ fun T x y => inj ?_, ha⟩
  rw [pa, pm, pm, pa, pa, MonObj.mul_comp]

theorem fibGrp : FibGrpSt := by
  intro R _ _ _ D J g Λ Hm χ ex fr hF
  obtain ⟨-, P', φ, w, u, hΛ, hg, -, hAH, -, -, hlift, hex, hfr⟩ := hF
  subst hΛ
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv hg (𝟙_ (Over (Sp ℂ))) (TF (R := R) ℂ).hom (Category.id_comp _).symm
  have hee : ∀ z, ex z = e (u.ex z) := fun z => Over.OverMorphism.ext ((hex z).trans (he _).symm)
  have hadd : ∀ z w, ex (z + w) = ex z * ex w := fun z w => by
    rw [hee, hee, hee, u.ex_add]
    exact map_mul e _ _
  have hker : ∀ z, ex z = 1 ↔ z ∈ u.Λ := fun z => by
    rw [hee, ← u.ker]
    exact e.map_eq_one_iff
  refine ⟨u.discrete, u.full, hAH.1, hAH.2.1, hAH.2.2.1, fun l m => FrameValue.chi_add P'.isLB hAH l m, hadd,
    fun y => ?_, hker, fun l z => ?_, fun f hf => ?_⟩
  · obtain ⟨x, hx⟩ := e.surjective y
    obtain ⟨z, rfl⟩ := u.ex_onto x
    exact ⟨z, (hee z).trans hx⟩
  · have hi := FrameValue.le_chartAt P'.isLB (u.ex z).left
    set i := FrameValue.chartAt P'.isLB (u.ex z).left
    have h₁ : u.ex (z + l) = u.ex z := by rw [u.ex_add, (u.ker _).2 l.2, _root_.mul_one]
    have h₂ : ex (z + l) = ex z := by rw [hee, hee, h₁]
    have a := hfr z i hi
    have b := hfr (z + l) i (by rw [h₁]; exact hi)
    rw [h₁, h₂] at b
    rw [a, b, hAH.2.2.2 l i z hi]
    simp only [hermForm]
    ring
  · obtain ⟨f', hf', hc⟩ := exists_pull_endo hg f hf
    obtain ⟨F, hF⟩ := hlift f' hf'
    have hF' : ∀ z, ex (F z) = ex z ≫ f := fun z => Over.OverMorphism.ext (by
      rw [Over.comp_left, hex, hex, hF, Over.comp_left, Category.assoc, hc, Category.assoc])
    refine ⟨F, hF', fun G hG => ?_⟩
    have hm : ∀ z, (G - F) z ∈ u.Λ := fun z => by
      rw [← hker]
      have h := hadd ((G - F) z) (F z)
      rw [LinearMap.sub_apply, sub_add_cancel, hG, hF'] at h
      exact mul_eq_right.1 h.symm
    haveI := u.discrete
    have hc : Continuous fun w => (⟨(G - F) w, hm w⟩ : u.Λ) :=
      (G - F).continuous_of_finiteDimensional.subtype_mk _
    refine sub_eq_zero.1 (LinearMap.ext fun z => ?_)
    have := PreconnectedSpace.constant inferInstance hc (x := z) (y := 0)
    simpa using congrArg Subtype.val this

end GlobalTheory.Ex.Arch

end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section
namespace GlobalTheory.Ex.Arch.FibCube
open GlobalTheory.FrameValue GlobalTheory.TorusExt

theorem vF_eq_genVal_mul {X Y Y' : Scheme.{0}} {L : LB X} {A : Over (Sp ℂ)} [GrpObj A] {L' : LB A.left} {g : ℕ}
    (u : HolUnif A L' g) (hL' : L'.IsLB) {Φ : A.left ⟶ X} {w : LB.Iso L' (L.pull Φ)} {K : Type} [Fintype K]
    {φ' : K → (Y' ⟶ A.left)} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y} (hψ : ∀ k, φ' k ≫ Φ = h ≫ φ k)
    {a : LB.Gen (LB.LinComb L' φ' ε)} (ha : a.IsGen) {t : LB.Gen (LB.LinComb L φ ε)} (H : PMaps w φ' φ ε a t h)
    {J : (Sp ℂ ⟶ X) → L.ι} (hJ : ∀ ψ : Sp ℂ ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) (fr : (Fin g → ℂ) → ℂˣ)
    (hfr : ∀ z i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L'.U i →
      (fr z : ℂ) = valAt' (u.ex z).left _ (w.s (fun _ => J ((u.ex z).left ≫ Φ), i)).val * u.fr i z)
    {r : Sp ℂ ⟶ Y'} {z : K → Fin g → ℂ} (hz : IsLift u φ' r z) :
    vF t (r ≫ h) J = genVal u hL' a r z * ((∏ k, fr (z k) ^ ε k : ℂˣ) : ℂ) := by
  let p : Sp ℂ := (default : PrimeSpectrum ℂ)
  let J' : (Sp ℂ ⟶ A.left) → L'.ι := chartAt hL'
  have hJ' : ∀ ψ : Sp ℂ ⟶ A.left, ⊤ ≤ ψ ⁻¹ᵁ L'.U (J' ψ) := le_chartAt hL'
  have e := congrArg (fun q => (((stalkUnits p).symm q : ℂˣ) : ℂ))
    (DegPull.pmaps_val hψ H r p (J := J) (J' := J') (fun ψ => hJ ψ trivial) (fun ψ => hJ' ψ trivial))
  have e₁ : vF a r J' = genVal u hL' a r z * frameProd u ε z (fun k => J' (r ≫ φ' k)) :=
    valAt'_gen hL' ha hz (le_wchart_chartAt hL' φ' r)
  have e₂ : ∀ v, (((stalkUnits p).symm (gw w (u.ex v).left p (J ((u.ex v).left ≫ Φ)) (J' (u.ex v).left)) : ℂˣ) : ℂ) *
      u.fr (J' (u.ex v).left) v = fr v := fun v => by
    rw [hfr v _ (hJ' _)]
    refine congrArg (· * _) ((stalkConst p).injective ?_)
    have m : ⊤ ≤ (u.ex v).left ⁻¹ᵁ ((L.pull Φ).U (fun _ => J ((u.ex v).left ≫ Φ)) ⊓ L'.U (J' (u.ex v).left)) :=
      fun y hy => ⟨mem_pull.2 (hJ ((u.ex v).left ≫ Φ) hy), hJ' _ hy⟩
    rw [← stalkUnits_val, MulEquiv.apply_symm_apply]
    exact (gs_unit (u.ex v).left p ((L.pull Φ).U (fun _ => J ((u.ex v).left ≫ Φ)) ⊓ L'.U (J' (u.ex v).left))
      (m trivial) _).symm.trans (gs_eq_stalkConst _ p m _)
  simp only [map_mul, map_prod, map_zpow, Units.val_mul] at e
  rw [GaugeValues.vF_eq hJ, GaugeValues.vF_eq hJ', e₁] at e
  rw [e, mul_left_comm]
  congr 1
  rw [frameProd, Units.coe_prod, Units.coe_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, ← mul_zpow, hz k, e₂]

theorem exists_cube_down {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'} [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left} (gp : IsGrpPullback G' G f F) {L : RigLB G}
    (c : CubicalStr G L) {L' : LB G'.left} (hL' : L'.IsLB) {w : LB.Iso L' (L.L.pull F)} (hw : w.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' (thφ G' (x3 G')) thε), a.IsGen ∧
      PMaps w (thφ G' (x3 G')) (thφ G (x3 G)) thε a c.t (cubeMapOf gp).F3 ∧
      LB.Gen.Corr L' _ _ (Y := (G2 G').left) _ _ (LB.pullGen L' (thφ G' (x3 G')) thε a (faceMap G' 0).left)
        (LB.oneGen L') := by
  have hψ : ∀ I : thK, thφ G' (x3 G') I ≫ F = (cubeMapOf gp).F3 ≫ thφ G (x3 G) I :=
    fun I => (cubeMapOf gp).psum_comm I.down
  obtain ⟨a, ha, H⟩ := DegPull.exists_pmaps ((isGen_iff w).1 hw) L.isLB hL' (ε := thε) (cubeMapOf gp).F3 hψ c.t c.isGen
  refine ⟨a, ha, H, corr_of_val hL' fun y J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := DegPull.exists_good' L.isLB y
  have e := DegPull.pmaps_val hψ H (lift (1 : G2 G' ⟶ G') (lift (x2 G' 0) (x2 G' 1))).left y hJ hJ'
  have q : ∀ a b c : G2 G' ⟶ G', (lift a (lift b c)).left ≫ (cubeMapOf gp).F3 =
      (lift (pushHom gp _ a) (lift (pushHom gp _ b) (pushHom gp _ c))).left := fun a b c =>
    hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp [x3] <;> rfl
  rw [q, map_one] at e
  have p := prod_cub (1 : G2 G' ⟶ G') (x2 G' 0) (x2 G' 1) (fun q => gw w q y (J (q ≫ F)) (J' q))
  rw [_root_.one_mul, _root_.one_mul] at p
  have e' := ((isCub_cubV c (T := Over.mk ((G2 G').hom ≫ f)) hJ).face _ _).symm.trans (e.trans (congrArg (· * _) p))
  refine (val_pull hJ' _ _ _).trans (Eq.trans ?_ (val_one _).symm)
  rw [Category.id_comp]
  apply Additive.ofMul.injective
  have e'' := congrArg Additive.ofMul e'
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at e'' ⊢
  refine Eq.trans ?_ e''.symm
  abel

end GlobalTheory.Ex.Arch.FibCube

namespace GlobalTheory.Ex.Arch
open GlobalTheory.FrameValue GlobalTheory.CubeValues

theorem fibCubeSt : Laws → FibCubeSt := by
  rintro - R _ _ _ D J g Λ Hm χ ex fr ⟨hJ, P', φ, w, u, hΛ, gp, hw, hAH, -, -, -, hex, hfr⟩ x y z
  obtain ⟨a, ha, H, hf⟩ := FibCube.exists_cube_down gp D.cub P'.isLB hw
  have e := FibCube.vF_eq_genVal_mul (L := D.P.L) (Φ := φ) (w := w) u P'.isLB (fun I : thK => (cubeMapOf gp).psum_comm I.down) ha H hJ fr
    (fun v i hi => by rw [← hex v]; exact hfr v i hi) (isLift_cube u ![x, y, z])
  replace e := e.trans ((congrArg (· * _) (genVal_cube_of_face P'.isLB hAH a ha hf _)).trans (_root_.one_mul _))
  have q : (pt3 u ![x, y, z]).left ≫ (cubeMapOf gp).F3 = (lift (ex x) (lift (ex y) (ex z))).left :=
    hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp [x3, pt3, hex] <;> rfl
  have p := prod_thK fun I => fr (∑ a ∈ I, ![x, y, z] a)
  simp only [sum_three, Finset.sum_singleton, Finset.sum_empty, Matrix.cons_val] at p
  rw [q] at e
  refine (congrArg (fun s : ℂ => s * fr (x + y) * fr (x + z) * fr (y + z) * fr 0)
    (e.trans (congrArg Units.val p))).trans ?_
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

end GlobalTheory.Ex.Arch
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section
namespace GlobalTheory.Ex.Arch.FibSym
open GlobalTheory.FrameValue GlobalTheory.TorusExt GlobalTheory.DegPull

theorem vF_down {A : Over (Sp ℂ)} [GrpObj A] {L' : LB A.left} {g : ℕ} {u : HolUnif A L' g} (hL' : L'.IsLB)
    {X Y Y' : Scheme.{0}} {L : LB X} {Φ : A.left ⟶ X} {K : Type} [Fintype K] {w : LB.Iso L' (L.pull Φ)}
    {φ' : K → (Y' ⟶ A.left)} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y} (hψ : ∀ k, φ' k ≫ Φ = h ≫ φ k)
    {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)} (ha : a.IsGen) (H : PMaps w φ' φ ε a t h)
    {J : (Sp ℂ ⟶ X) → L.ι} (hJ : ∀ ψ : Sp ℂ ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) {fr : (Fin g → ℂ) → ℂˣ}
    (hfr : ∀ z i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L'.U i →
      (fr z : ℂ) = valAt' (u.ex z).left _ (w.s (fun _ => J ((u.ex z).left ≫ Φ), i)).val * u.fr i z)
    {y : Sp ℂ ⟶ Y'} {z : K → Fin g → ℂ} (hz : IsLift u φ' y z) :
    vF t (y ≫ h) J = genVal u hL' a y z * ∏ k, (fr (z k) : ℂ) ^ ε k := by
  let p : Sp ℂ := IsLocalRing.closedPoint ℂ
  have gJ : ∀ q : Sp ℂ, Good L q J := fun q ψ => hJ ψ trivial
  have gJ' : ∀ q : Sp ℂ, Good L' q (chartAt hL') := fun q ψ => le_chartAt hL' ψ trivial
  have key : ∀ {Z : Scheme.{0}} (x : Sp ℂ ⟶ Z) (U : Z.Opens) (f : Γ(Z, U)ˣ), ⊤ ≤ x ⁻¹ᵁ U →
      (gm x p U f).val = stalkConst p (valAt' x U f.val) := fun x U f hU =>
    (gs_unit x p U (hU trivial) f).symm.trans (gs_eq_stalkConst x p hU _)
  have e := congrArg Units.val (pmaps_val hψ H y p (gJ p) (gJ' p))
  have e₁ : (val t (y ≫ h) p J).val = stalkConst p (vF t (y ≫ h) J) :=
    key _ _ _ (fun q _ => (gJ q).mem φ (y ≫ h))
  have e₂ : (val a y p (chartAt hL')).val = stalkConst p (genVal u hL' a y z *
      frameProd u ε z fun k => chartAt hL' (y ≫ φ' k)) :=
    (key _ _ _ (le_wchart_chartAt hL' φ' y)).trans (congrArg _ (valAt'_gen hL' ha hz (le_wchart_chartAt hL' φ' y)))
  have hm : ∀ x : Sp ℂ ⟶ A.left, ⊤ ≤ x ⁻¹ᵁ ((L.pull Φ).U (fun _ => J (x ≫ Φ)) ⊓ L'.U (chartAt hL' x)) :=
    fun x q _ => ⟨mem_pull.2 (gJ q (x ≫ Φ)), gJ' q x⟩
  have e₃ : ∀ x : Sp ℂ ⟶ A.left, Geo.Tor.gw w x p (J (x ≫ Φ)) (chartAt hL' x) = stalkUnits p
      (Units.mk0 (valAt' x _ (w.s (fun _ => J (x ≫ Φ), chartAt hL' x)).val)
        (CubeValues.val_unit_ne_zero x SymmetricSemicharacter.valueRules (hm x) _)) := fun x =>
    Units.ext (key x _ _ (hm x))
  rw [Units.val_mul, e₁, e₂] at e
  simp only [e₃, ← map_zpow, ← map_prod] at e
  rw [stalkUnits_val, ← map_mul] at e
  rw [(stalkConst p).injective e, mul_left_comm, frameProd, Units.coe_prod, ← Finset.prod_mul_distrib]
  refine congrArg _ (Finset.prod_congr rfl fun k _ => ?_)
  rw [Units.val_zpow_eq_zpow_val, ← mul_zpow, hz k, hfr (z k) _ (le_chartAt hL' _)]
  rfl

theorem exists_sym_pmaps {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] [IsCommMonObj G]
    [IsCommMonObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left} (gp : IsGrpPullback G' G f F) {L : LB G.left}
    {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB) {w : LB.Iso L' (L.pull F)} (hw : PGen w)
    (s : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) (hs : s.IsGen)
    (hr : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ s (eSec G)) (LB.oneGen L)) :
    ∃ s' : LB.Gen (LB.LinComb L' (K := Fin 2) ![(ι[G']).left, 𝟙 G'.left] ![1, -1]), s'.IsGen ∧
      LB.Gen.Corr L' _ _ _ _ (LB.pullGen L' _ _ s' (eSec G')) (LB.oneGen L') ∧
      (∀ k : Fin 2, ![(ι[G']).left, 𝟙 G'.left] k ≫ F = F ≫ ![(ι[G]).left, 𝟙 G.left] k) ∧ PMaps w _ _ _ s' s F := by
  have hι : (ι[G']).left ≫ F = F ≫ (ι[G]).left := by
    have e := congrArg (fun q => q.left) (map_inv (pushHom gp G') (𝟙 G'))
    simp only [Hom.inv_def, Category.id_comp] at e
    refine Eq.trans e ?_
    show (𝟙 _ ≫ F) ≫ _ = _
    rw [Category.id_comp]
  have hψ : ∀ k : Fin 2, ![(ι[G']).left, 𝟙 G'.left] k ≫ F = F ≫ ![(ι[G]).left, 𝟙 G.left] k := fun k => by
    fin_cases k
    · exact hι
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨s', hs', H⟩ := exists_pmaps hw hL hL' F hψ s hs
  refine ⟨s', hs', corr_of_val hL' fun y J' hJ' => ?_, hψ, H⟩
  obtain ⟨J, hJ⟩ := exists_good' hL y
  have e := pmaps_val hψ H (eSec G') y hJ hJ'
  have e₀ : eSec G' ≫ (ι[G']).left = eSec G' := by
    rw [eSec, ← Over.comp_left]; simp
  have he : eSec G' ≫ F = f ≫ eSec G := (cubeMapOf gp).e_comm
  rw [Fin.prod_univ_two] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e₀, Category.comp_id, zpow_one, zpow_neg,
    mul_inv_cancel, _root_.one_mul] at e
  refine (val_pull hJ' _ _ _).trans (Eq.trans ?_ (val_one _).symm)
  rw [Category.id_comp, ← e, he]
  exact (val_pull hJ s (eSec G) f).symm.trans ((val_corr hJ hr f).trans (val_one _))

theorem fibSymSt : Laws → FibSymSt := by
  intro _ R _ _ _ D J g Λ Hm χ ex fr hF
  obtain ⟨hJ, P', φ, w, u, rfl, gp, hw, hAH, -, -, -, hex, hfr⟩ := hF
  obtain ⟨s, hs, hr, hψ, H⟩ := exists_sym_pmaps gp D.P.isLB P'.isLB ((isGen_iff w).1 hw) D.sym D.sym_gen D.sym_rig
  obtain ⟨h₁, h₂⟩ := genVal_sym P'.isLB hAH s hs hr
  refine ⟨fun x => ?_, h₂⟩
  have e := vF_down P'.isLB hψ hs H hJ (fr := fr) (fun z i hi => hex z ▸ hfr z i hi) (isLift_sym u x)
  rw [h₁, Fin.prod_univ_two] at e
  rw [hex x]
  refine (congrArg (· * (fr x : ℂ)) e).trans ?_
  simp

end GlobalTheory.Ex.Arch.FibSym
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.Ex.Arch
open GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter GlobalTheory.EigenNorm GlobalTheory.FrameValue

theorem val_iso_chart {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} (hL' : L'.IsLB) {F : X' ⟶ X}
    {w : LB.Iso L' (L.pull F)} (hw : w.IsGen) (x : Sp ℂ ⟶ X') (j j' : L.ι) (i : L'.ι)
    (hj : ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j) (hj' : ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j') (hi : ⊤ ≤ x ⁻¹ᵁ L'.U i) :
    valAt' x _ (w.s (fun _ => j, i)).val =
      valAt' (x ≫ F) (L.U j ⊓ L.U j') (L.g j j').val * valAt' x _ (w.s (fun _ => j', i)).val := by
  have a : ⊤ ≤ x ⁻¹ᵁ L.wchart (fun _ : PUnit => F) (fun _ => j) := (le_preimage_wchart x L _ _).2 fun _ => hj
  have a' : ⊤ ≤ x ⁻¹ᵁ L.wchart (fun _ : PUnit => F) (fun _ => j') := (le_preimage_wchart x L _ _).2 fun _ => hj'
  have b := (le_preimage_inf x _ _).2 ⟨a, hi⟩
  have b' := (le_preimage_inf x _ _).2 ⟨a', hi⟩
  have c := (le_preimage_inf x _ _).2 ⟨b, b'⟩
  refine (val_sec x (genSec w hw) (fun _ => j, i) (fun _ => j', i) b b').trans (congrArg₂ (· * ·) ?_ rfl)
  have e₁ := val_linComb x valueRules L (fun _ : PUnit => F) (fun _ => 1) (fun _ => j) (fun _ => j') a a'
  rw [Fintype.prod_unique, zpow_one] at e₁
  have e₂ : valAt' x (L'.U i ⊓ L'.U i) (L'.g i i).val = 1 := by
    obtain ⟨e, he⟩ := (valueRules X' x).2.1 _ hi
    rw [← val_res x valueRules (le_inf le_rfl le_rfl) hi, hL'.g_self i, he]
    exact map_one e
  obtain ⟨e, he⟩ := (valueRules X' x).2.1 _ c
  refine (val_unit_mul x valueRules c _ _).trans ?_
  refine (congrArg₂ (· * ·) ((val_res x valueRules _ c _).trans e₁) ((he _).trans ((map_units_inv e _).trans
    (congrArg (·⁻¹) ((he _).symm.trans ((val_res x valueRules _ c _).trans e₂)))))).trans ?_
  simp

theorem fibSec : FibSecSt := by
  intro R _ _ _ D J g Λ Hm χ ex fr h s
  obtain ⟨hJ, P', φ, w, u, hΛ, -, hw, -, -, -, -, hex, hfr⟩ := h
  refine ⟨fun z => sF s (ex z).left J / fr z, fun z₀ => ?_, fun z => (div_mul_cancel₀ _ (fr z).ne_zero).symm⟩
  obtain ⟨i, hi⟩ : ∃ i, ⊤ ≤ (u.ex z₀).left ⁻¹ᵁ P'.L.U i := ⟨_, le_chartAt P'.isLB _⟩
  obtain ⟨j, hj⟩ : ∃ j, ⊤ ≤ ((u.ex z₀).left ≫ φ) ⁻¹ᵁ D.P.L.U j := ⟨_, hJ _⟩
  have ch : ∀ (y : Sp ℂ ⟶ D.P.A.left) (k : D.P.L.ι), ⊤ ≤ y ⁻¹ᵁ D.P.L.U k →
      ⊤ ≤ y ⁻¹ᵁ D.P.L.wchart (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => k) := fun y k hk =>
    (le_preimage_wchart y _ _ _).2 fun _ => by rwa [Category.comp_id]
  have a : ⊤ ≤ (u.ex z₀).left ⁻¹ᵁ (D.P.L.wchart (fun _ : PUnit => φ) (fun _ => j) ⊓ P'.L.U i) :=
    (le_preimage_inf _ _ _).2 ⟨(le_preimage_wchart _ _ _ _).2 fun _ => hj, hi⟩
  obtain ⟨o₁, d₁⟩ := u.hol (φ ⁻¹ᵁ D.P.L.wchart (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => j))
    ((φ.app _).hom (s.f fun _ => j))
  obtain ⟨o₂, d₂⟩ := u.hol _ (w.s (fun _ => j, i)).val
  have n₂ := o₂.mem_nhds a
  have d := (d₁.differentiableAt (o₁.mem_nhds (ch _ j hj))).fun_mul (((d₂.differentiableAt n₂).fun_mul
    ((u.fr_hol i).differentiableAt ((u.hol _ 0).1.mem_nhds hi))).fun_inv
    (mul_ne_zero (val_unit_ne_zero _ valueRules a _) (u.fr_ne i _ hi)))
  refine d.congr_of_eventuallyEq ?_
  filter_upwards [n₂] with z hz
  obtain ⟨h₁, h₂⟩ := (le_preimage_inf _ _ _).1 hz
  have h₃ := (le_preimage_wchart _ _ _ _).1 h₁ PUnit.unit
  have e₀ : sF s (ex z).left J = valAt' (ex z).left _ (s.f fun _ => J (ex z).left) := by
    rfl
  have e₁ := val_sec (ex z).left s (fun _ => J (ex z).left) (fun _ => j) (ch _ _ (hJ _)) (ch _ _ (hex z ▸ h₃))
  have e₂ := val_linComb (ex z).left valueRules D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => ((1 : ℕ) : ℤ))
    (fun _ => J (ex z).left) (fun _ => j) (ch _ _ (hJ _)) (ch _ _ (hex z ▸ h₃))
  rw [Fintype.prod_unique, Nat.cast_one, zpow_one, Category.comp_id] at e₂
  have e₃ := val_iso_chart P'.isLB hw (u.ex z).left (J (ex z).left) j i (hex z ▸ hJ _) h₃ h₂
  have n := val_unit_ne_zero (ex z).left valueRules ((le_preimage_inf _ _ _).2 ⟨hJ _, hex z ▸ h₃⟩)
    (D.P.L.g (J (ex z).left) j)
  have e₄ := (valueRules _ (u.ex z).left).2.2.2.1 _ φ _ (s.f fun _ => j)
  rw [← hex z] at e₃ e₄
  rw [e₀, e₁, hfr z i h₂, e₃, _root_.mul_assoc]
  exact (congrArg (fun q => q * _ / _) e₂).trans ((mul_div_mul_left _ _ n).trans ((div_eq_mul_inv _ _).trans
    (congrArg₂ (· * ·) e₄.symm rfl)))

end GlobalTheory.Ex.Arch
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section
namespace GlobalTheory.Ex.Arch

open GlobalTheory.PointUnif GlobalTheory.EigenSplit in

theorem fibLie_of_laws : Laws → FibLieSt := by
  intro _ R _ _ _ D J g Λ Hm χ ex fr hfib O _ act F hF τ n hn
  obtain ⟨-, P', φ, w, u, -, hφ, -, -, h1, h2, -, hex, -⟩ := hfib
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.LiePull.exists_pushEquiv hφ (𝟙_ _) (TF (R := R) ℂ).hom (Category.id_comp _).symm
  have he := isExp_push hφ u h1 h2 Φ hΦ
  have hx : ∀ z, Φ (u.ex z) = ex z := fun z => Over.OverMorphism.ext ((hΦ _).trans (hex z).symm)
  have hker : ∀ z, Φ (u.ex z) = 1 ↔ z ∈ u.Λ := fun z => (map_eq_one_iff Φ Φ.injective).trans (u.ker z)
  have hF' : ∀ a z, Φ (u.ex (F a z)) = Φ (u.ex z) ≫ act.act a := fun a z => by
    rw [hx, hx]; exact hF a z
  obtain ⟨ρ, hρ⟩ := he.exists_rep act u.Λ u.discrete hker fun a => ⟨F a, hF' a⟩
  have hρF : ∀ a, ρ a = F a := fun a => by
    refine sub_eq_zero.1 (linear_eq_zero_of_discrete u.Λ u.discrete _ fun z => (hker _).1 ?_)
    have := he.1 ((ρ a - F a) z) (F a z)
    simp only [LinearMap.sub_apply, sub_add_cancel] at this
    rw [hρ, ← hF'] at this
    exact mul_eq_right.1 this.symm
  have hy : (TF (R := R) ℂ).hom = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R _)) :=
    (Spec.map_comp _ _).symm
  rw [← hy] at hn
  have hE : (⨅ a, (F a).eigenspace (τ a) : Submodule ℂ (Fin g → ℂ)) = eigenSub ρ τ := by
    ext z
    simp only [mem_eigenSub, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, hρF]
  rw [hE]
  exact he.finrank_eigenSub act ρ hρ hn

end GlobalTheory.Ex.Arch
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

namespace GlobalTheory.ActValues
open GlobalTheory.TorusExt GlobalTheory.ValuesExist

section Val
variable {F : Type} [Field F] {X Y Y' : Scheme.{0}} {L : LB X} {K K' K'' : Type} [Fintype K] [Fintype K'] [Fintype K'']
  {J : (Sp F ⟶ X) → L.ι}

theorem vF_corr {z : Sp F} (hJ : Good L z J) {φ : K → (Y' ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {φ'' : K'' → (Y' ⟶ X)} {ε'' : K'' → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} {u : LB.Gen (LB.LinComb L φ' ε')}
    {t' : LB.Gen (LB.LinComb L φ'' ε'')} {h : Y' ⟶ Y}
    (H : LB.Gen.Corr L _ _ _ _ (LB.mulGen L _ _ _ _ t (LB.pullGen L _ _ u h)) t') (r : Sp F ⟶ Y') :
    vF t r J * vF u (r ≫ h) J = vF t' r J := by
  have e := val_corr hJ H r
  rw [val_mul hJ, val_pull hJ] at e
  rw [← coe_val t r hJ, ← coe_val u _ hJ, ← coe_val t' r hJ, ← e, map_mul, Units.val_mul]
end Val

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {N : NumD F} (ν : NumOf D F N)

theorem good (z : Sp F) : Good D.P.L z ν.J := fun ψ => ν.good ψ trivial

theorem psi_eq (y : N.X) :
    (N.ψ y : F) = vF (LB.mulGen D.P.L _ _ _ _ (D.psi (ν.eX y)) D.rigK) (jFK (R := R) F) ν.J := by
  let z : Sp F := IsLocalRing.closedPoint F
  have hJ := good ν z
  rw [ν.ψ_eq, ← coe_val _ _ hJ, ← coe_val _ _ hJ, ← coe_val _ _ hJ, ← Units.val_mul, ← map_mul]
  exact congrArg (fun q => (((stalkUnits z).symm q : Fˣ) : F))
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm

theorem tau_eq (a b : N.X) : (N.τ a b : F) = vF (D.tau (ν.eX a) (ν.eX b)) (jFK (R := R) F) ν.J := by
  let z : Sp F := IsLocalRing.closedPoint F
  have hJ := good ν z
  let e := (stalkUnits z).symm
  let ρ : ((Sp F).presheaf.stalk z)ˣ := val (Z := Sp F) D.rigK (jFK (R := R) F) z ν.J
  let p : D.X → ((Sp F).presheaf.stalk z)ˣ := fun χ => val (Z := Sp F) (D.psi χ) (jFK (R := R) F) z ν.J
  have hτ : ∀ a b, val (Z := Sp F) (D.tau a b) (jFK (R := R) F) z ν.J = p (a + b) * (p a)⁻¹ * (p b)⁻¹ * ρ⁻¹ := fun a b =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  have hψ : ∀ y, N.ψ y = e (p (ν.eX y) * ρ) := fun y => Units.ext ((psi_eq ν y).trans
    ((coe_val _ _ hJ).symm.trans (congrArg (fun q => ((e q : Fˣ) : F)) (val_mul hJ _ _ _))))
  refine Eq.trans ?_ (coe_val _ _ hJ)
  rw [hτ, NumD.τ, hψ, hψ, hψ, ← map_div, ← map_div, map_add]
  refine congrArg (fun q => ((e q : Fˣ) : F)) (Additive.ofMul.injective ?_)
  simp only [ofMul_mul, ofMul_inv, ofMul_div]
  abel

theorem brAct : Laws → BrActSt := by
  intro hL R _ _ D _ _ F _ _ _ N ν O _ _ _ oa
  have hJ := good ν (IsLocalRing.closedPoint F)
  refine ⟨fun a => ?_, fun a => ?_, fun w₀ hw => ?_⟩
  · have := oa.onB.hom a
    have := oa.onB.hom (star a)
    obtain ⟨r, hr, r₀⟩ := exists_ros hL.globalFns D.P.isAb D.P.isLB _ _ (oa.onB.rosati a)
    refine ⟨r, ⟨hr, r₀⟩, fun y y' => ?_⟩
    have h := vF_corr hJ (oa.tau_bal a r hr r₀ (ν.eX y) (ν.eX y')) (jFK (R := R) F)
    have h2 : jFK (R := R) F ≫ D.pt2 (ν.eX y) (ν.eX y') = (lift (ν.eA (N.c y)) (ν.eA (N.c y'))).left := by
      rw [ν.c_eq, ν.c_eq]
      let κ : TF (R := R) F ⟶ TK R := Over.homMk (jFK (R := R) F) rfl
      refine congrArg CommaMorphism.left (show κ ≫ lift _ _ = _ from ?_)
      simp only [comp_lift, comp_toUnit_assoc]
    rw [tau_eq ν, tau_eq ν, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, ← h2]
    exact h
  · have := oa.onB.hom a
    have := oa.onB.hom (star a)
    have hr := oa.onB.rosati (star a)
    rw [star_star] at hr
    obtain ⟨r, hr, r₀⟩ := exists_ros hL.globalFns D.P.isAb D.P.isLB _ _ hr
    refine ⟨r, ⟨hr, r₀⟩, fun g g' c c' hc hc' hg => ⟨by rw [hc.1, hc'.1, hg.1], fun χ => ?_⟩⟩
    have h := vF_corr hJ (hg.2 r hr r₀ (ν.eX χ)) (𝟙 (Sp F))
    rw [hc'.2, hc.2, AddEquiv.apply_symm_apply, ν.c_eq, hc.1]
    exact h.symm.trans (congrArg (fun q => _ * vF r q ν.J) (Category.id_comp _))
  · obtain ⟨t, ht, t₀, hy⟩ := hw
    refine ⟨t, ⟨ht, t₀⟩, fun y => ?_⟩
    have h := vF_corr hJ (hy (ν.eX y)) (jFK (R := R) F)
    have h2 : jFK (R := R) F ≫ D.xK (ν.eX y) = (ν.eA (N.c y)).left := by
      rw [ν.c_eq]
      exact (Category.assoc _ _ _).symm
    rw [tau_eq ν, psi_eq ν, AddEquiv.apply_symm_apply, ← h2]
    exact h

end GlobalTheory.ActValues
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

namespace GlobalTheory.Ex.Arch

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
open scoped CategoryTheory.Obj BigOperators in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.Ex.Arch.towerSt_of : _root_.GlobalTheory.Ex.BrGtSt → _root_.GlobalTheory.Ex.BrWpSt → _root_.GlobalTheory.Ex.Arch.PtSt → _root_.GlobalTheory.Ex.Arch.QkSt → _root_.GlobalTheory.Ex.Arch.WpSt → _root_.GlobalTheory.Ex.Arch.TowerSt := by
  intro hGt hWp hPt hQk hWA
  unfold _root_.GlobalTheory.Ex.BrGtSt _root_.GlobalTheory.Ex.AllN at hGt
  unfold _root_.GlobalTheory.Ex.BrWpSt _root_.GlobalTheory.Ex.AllN at hWp
  unfold _root_.GlobalTheory.Ex.Arch.PtSt _root_.GlobalTheory.Ex.Arch.AllDict at hPt
  unfold _root_.GlobalTheory.Ex.Arch.QkSt _root_.GlobalTheory.Ex.Arch.AllDict at hQk
  unfold _root_.GlobalTheory.Ex.Arch.WpSt _root_.GlobalTheory.Ex.Arch.AllDict at hWA
  beta_reduce at hGt hWp hPt hQk hWA
  unfold _root_.GlobalTheory.Ex.Arch.TowerSt _root_.GlobalTheory.Ex.AllD
  intro E _ _ _ H D R _ _ _ A B dd hl
  letI := H.starRing
  have hG := hGt R A.D₀ A.even A.bimult ℂ A.N A.ν
  have hW := hWp R A.D₀ A.even A.bimult ℂ A.N A.ν
  have hV := hPt (𝓞 E) A.N _ dd
  have hL := hQk (𝓞 E) A.N _ dd
  have hE := hWA (𝓞 E) A.N _ dd
  have hq := A.hq
  have hT := _root_.GlobalTheory.NestQVal.qval_add_tower E H D R A.D₀ A.oa A.even A.bimult ℂ A.I A.N A.ν A.q
    hG.1 hG.2.2.1 (fun k => ⟨(hG.2.2.2.2 k).1, (hG.2.2.2.2 k).2.2⟩) hq
  choose! f hf using fun n (hn : 0 < n) (a : D.La) => (hL n hn).1 (A.q n a)
  have hpow : ∀ (m : ℕ) v g, dd.IsPt v g → dd.IsPt (m • v) (g ^ m) := by
    obtain ⟨g₀, hg₀, hu⟩ := hV.1 0
    have h00 := hV.2.2.1 0 0 g₀ g₀ hg₀ hg₀
    rw [add_zero] at h00
    have hg₁ : g₀ = 1 := mul_eq_left.1 (hu _ h00)
    intro m v g hg
    induction m with
    | zero => simpa [hg₁] using hg₀
    | succ k ih => simpa [succ_nsmul, pow_succ] using hV.2.2.1 _ _ _ _ ih hg
  refine ⟨f, ?_, hf⟩
  unfold _root_.GlobalTheory.Ex.Arch.IsTower
  intro n hn
  obtain ⟨-, hRep, hmul, hmod⟩ := hL n hn
  have hQn := (hG.2.2.2.2 n).2.2
  have hadd : ∀ a b, ∃ e, f n (a + b) = f n a + f n b + n • e := fun a b =>
    (hmod _ _ _ _ (hmul _ _ _ _ (hf n hn a) (hf n hn b)) (hf n hn (a + b))).1 (hT.1 n hn a b)
  refine ⟨hadd, ?_, ?_, ?_, ?_, ?_⟩
  · intro c a
    obtain ⟨Q, hQy, hQg, hQe⟩ := A.I.lin n hn c a
    obtain ⟨p', hp', -⟩ := hRep (c • f n a)
    obtain ⟨hya, hga⟩ := hq n a
    obtain ⟨c'', hc'', -⟩ := hG.1 Q.g
    have hRa := hf n hn a
    have hv := hl.2 c _ _ _ _ _ hga hc'' hQg hRa.2
    rw [map_smul, ← _root_.GlobalTheory.AnArc.degeneratingTori_basePeriodMap_smul] at hv
    have hc : c'' = (p' : Multiplicative A.N.X × A.N.Gt).2 := (hV.1 _).unique hv hp'.2
    have hQp : A.ν.QPt Q p' := by
      refine ⟨?_, hc ▸ hc''⟩
      rw [hp'.1, _root_.GlobalTheory.AnArc.La.smul_y, hl.1, hQy, ← hya, hRa.1]
      unfold _root_.GlobalTheory.Ex.ArcF.act
      simp
    exact (hmod _ _ _ _ hp' (hf n hn (c • a))).1 ((hQn _ _ _ _ hQp (hq n (c • a))).1 hQe)
  · intro a
    obtain ⟨e₀, he₀⟩ : ∃ e, f n 0 = n • e := by
      obtain ⟨e, he⟩ := hadd 0 0
      rw [add_zero] at he
      refine ⟨-e, ?_⟩
      rw [smul_neg, eq_neg_iff_add_eq_zero]
      calc f n 0 + n • e = (f n 0 + f n 0 + n • e) - f n 0 := by abel
        _ = 0 := by rw [← he, sub_self]
    have key : (∃ e, f n 0 = f n a + n • e) ↔ ∃ b, a = n • b := by
      rw [← hmod _ _ _ _ (hf n hn a) (hf n hn 0), ← hQn _ _ _ _ (hq n a) (hq n 0), A.I.ker n hn a 0]
      simp
    rw [← key]
    constructor
    · rintro ⟨e, he⟩
      exact ⟨e₀ - e, by rw [he₀, he, smul_sub]; abel⟩
    · rintro ⟨e, he⟩
      exact ⟨e₀ - e, by rw [smul_sub, ← he₀, he]; abel⟩
  · intro x
    obtain ⟨p, hp, -⟩ := hRep x
    obtain ⟨P, hP⟩ := (hG.2.2.2.2 n).2.1 p
    obtain ⟨a, ha⟩ := A.I.onto n hn P
    obtain ⟨e, he⟩ := (hmod _ _ _ _ (hf n hn a) hp).1 ((hQn _ _ _ _ (hq n a) hP).1 ha)
    exact ⟨a, e, he⟩
  · intro m hm a
    have hnm : 0 < n * m := Nat.mul_pos hn hm
    obtain ⟨p, hp, -⟩ := hRep (f (n * m) a)
    have hR := hf (n * m) hnm a
    have h1 : (p : Multiplicative A.N.X × A.N.Gt).1 = (A.q (n * m) a : Multiplicative A.N.X × A.N.Gt).1 := by
      apply Multiplicative.toAdd.injective
      rw [hp.1, hR.1]
    have h2 : (p : Multiplicative A.N.X × A.N.Gt).2 = (A.q (n * m) a : Multiplicative A.N.X × A.N.Gt).2 ^ m := by
      apply (hV.1 _).unique hp.2
      convert hpow m _ _ hR.2 using 1
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
      congr 1
      have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      have : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
      push_cast
      field_simp
    obtain ⟨e, he⟩ := (hmod _ _ _ _ hp (hf n hn a)).1 (hT.2 n m hn hm a p h1 h2)
    exact ⟨-e, by rw [he, smul_neg]; abel⟩
  · intro a b
    rw [(hW n hn _ _ _ _ _ (hq n a) (hq n b)).1 (A.I.isom n hn a b)]
    exact hE n hn _ _ _ _ (hf n hn a) (hf n hn b)

end GlobalTheory.Ex.Arch
end

section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.Ex.Arch

variable {E : Type} [Field E] [NumberField E]

theorem exists_types (m : (E →+* ℂ) → ℕ) : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)),
    (∀ φ, Nat.card {i // ty i = φ} = m φ) ∧ ∀ a : E, ∑ i, ty i a = ∑ φ : E →+* ℂ, (m φ : ℂ) * φ a := by
  classical
  let e := (Fintype.equivFin (Σ φ : E →+* ℂ, Fin (m φ))).symm
  refine ⟨_, fun i => (e i).1, fun φ => ?_, fun a => ?_⟩
  · rw [Nat.card_congr (e.subtypeEquiv (q := fun k => k.1 = φ) fun _ => Iff.rfl),
      Nat.card_congr (Equiv.sigmaSubtype φ)]
    simp
  · rw [e.sum_comp fun k => k.1 a, Fintype.sum_sigma]
    simp

theorem trace_eq_sum_finrank {g : ℕ} (ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (a : 𝓞 E) :
    LinearMap.trace ℂ _ (ρ a) = ∑ φ : E →+* ℂ,
      (Module.finrank ℂ (EigenSplit.eigenSub ρ (φ.comp (algebraMap (𝓞 E) E))) : ℂ) * φ (a : E) := by
  obtain ⟨g', ty, hc, hs⟩ :=
    exists_types fun φ : E →+* ℂ => Module.finrank ℂ (EigenSplit.eigenSub ρ (φ.comp (algebraMap (𝓞 E) E)))
  obtain ⟨h, hh⟩ := PointUnif.exists_equiv_of_finrank_eq (PointUnif.isSplitting_embeddings (E := E))
    (PointUnif.diagRep ty) ρ fun φ => by rw [PointUnif.finrank_eigenSub_diagRep, hc]
  have h1 : ρ a = h.conj (PointUnif.diagRep ty a) := LinearMap.ext fun v => by simp [LinearEquiv.conj_apply, hh]
  have h2 : PointUnif.diagRep ty a = Matrix.toLin' (Matrix.diagonal fun i => ty i (a : E)) :=
    LinearMap.ext fun z => funext fun i => by simp [PointUnif.diagRep_apply, Matrix.mulVec_diagonal]
  rw [h1, LinearMap.trace_conj', h2, ← hs]
  simp

theorem typeSt : TypeSt := by
  intro E _ _ _ H D
  let _ := H.starRing
  intro B hB
  classical
  obtain ⟨g, ty, hc, hs⟩ := exists_types fun φ : E →+* ℂ => if φ (H.rt : E) = H.rt0 then D.p else D.q
  have hbar : ∀ a : 𝓞 E, ∑ τ : E →+* ℂ, τ (H.bar a : E) = ∑ τ : E →+* ℂ, τ (a : E) := fun a => by
    refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro τ _; exact Finset.mem_univ _
    · intro τ _; exact Finset.mem_univ _
    · intro τ _; ext x; simp
    · intro τ _; ext x; simp
    · intro τ _
      rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]
  have := HomTrace.finite_hom B.X
  obtain ⟨h, hh⟩ := PeriodNonempty.exists_diag B.actV ty fun a => by
    let f : (B.X →+ ℂ) →ₗ[ℂ] (B.X →+ ℂ) := LinearMap.fst ℂ _ _ ∘ₗ B.actV a ∘ₗ LinearMap.inl ℂ _ _
    have h1 : B.actV a = f.prodMap (B.F a) := LinearMap.ext fun v => rfl
    rw [h1, LinearMap.trace_prodMap', HomTrace.trace_eq_finrank_mul_sum E B.X (H.bar a) f fun _ _ => rfl, hbar,
      trace_eq_sum_finrank, hs, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun φ _ => ?_
    have h2 : Module.finrank ℂ (EigenSplit.eigenSub B.F (φ.comp (algebraMap (𝓞 E) E))) + Module.finrank (𝓞 E) B.X =
        if φ (H.rt : E) = H.rt0 then D.p else D.q := by
      have h3 := hB (φ.comp (algebraMap (𝓞 E) E))
      by_cases hφ : φ (H.rt : E) = H.rt0
      · rw [if_pos hφ]; exact h3.trans (if_pos hφ)
      · rw [if_neg hφ]; exact h3.trans (if_neg hφ)
    rw [← h2]
    push_cast
    ring
  exact ⟨g, ty, h, fun φ => ⟨fun hφ => (hc φ).trans (if_pos hφ), fun hφ => (hc φ).trans (if_neg hφ)⟩, hh⟩

end GlobalTheory.Ex.Arch

end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.Ex.Arch

theorem tripleSt_of_laws : Laws → ThetaUnifAV → TripleSt := by
  intro laws hθ E _ _ _ H D La _ _ EF g ty P Hm hty hbij hadj hlin hinj hdisc hspan hH hpos him
  letI := H.starRing
  obtain ⟨D', e, -, -, hEF⟩ := PeriodDatum.exists_datum E H La EF D.p D.q g ty P Hm hty hbij hadj hlin hinj hdisc hspan
    hH hpos him
  let P' : D'.La →+ (Fin g → ℂ) := P.comp e.toAddEquiv.toAddMonoidHom
  have hP' : ∀ a, P' a = P (e a) := fun _ => rfl
  have hr : P'.range = P.range := by
    ext z
    exact ⟨fun ⟨a, h⟩ => ⟨e a, h⟩, fun ⟨a, h⟩ => ⟨e.symm a, by rw [hP', e.apply_symm_apply, h]⟩⟩
  have hper : IsPeriod D' ty P' := by
    refine ⟨fun a x i => ?_, hinj.comp e.injective, by rw [hr]; exact hdisc, ?_, Hm, hH, hpos, fun x y => ?_⟩
    · rw [hP', hP', map_smul, hlin]
    · rw [← hspan]; exact congrArg _ (congrArg SetLike.coe hr)
    · rw [hP', hP', him, hEF]
  obtain ⟨T, L, u, hA, hdim, hamp, hK, ht₁, ht₂, hker, hact, hW⟩ :=
    PeriodPoint.exists_triple laws Moduli.cube_of_isLB principalTorus_algebraic (exists_isMonHom_of_map_lattice hθ laws)
      (lbIso_cubeLB_of_pairing_adjoint laws) (PrimNorm.exists_primitive_normalisation laws.globalFns)
      (kTriv_of_descent laws) relAmple_finite_pow_iso D' ty P' hper
  let Q : PolAV (Sp ℂ) :=
    { A := T.G, isAb := hA, g := g, smoothDim := hdim, L := T.PP.L, isLB := T.PP.isLB,
      rigid := ⟨T.PP.rig, T.PP.rigGen⟩, sym := CechPic.sym_of_isSymmetric T.PP T.sym, ample := hamp, ktriv := hK }
  let oa : Q.OAct (𝓞 E) :=
    { T.act.toRingAct with
      rosati := fun a _ => ⟨⊤, trivial, by
        obtain ⟨r, hr⟩ := NormRos.exists_gen_rosati T.PP.isLB _ _ (T.adj a)
        exact ⟨_, DVR.pullGen_isGen _ _ _ _ hr _⟩⟩ }
  obtain ⟨v, hv, heig⟩ := exists_lieBasis_of_holUnif T.G L g u hA.smooth ht₁ ht₂
  have hdet : DetCond D T.act (spMap (RingHom.id ℂ)) H.rt0 :=
    PeriodPoint.detCond_of_eigenbasis lieMult_of_eigenbasis D T ty hty v hv
      (fun i a => heig _ _ (T.act.hom a) (hact a) i) (RingHom.id ℂ)
  rw [show spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) from Spec.map_id _] at hdet
  refine ⟨Q, oa, L, u, rfl, T.prim, hdet, ht₁, ht₂, fun z => hr ▸ hker z, hact, fun k a b c hk hc => ?_⟩
  have := hW k (e.symm a) (e.symm b) c hk (by rw [hEF, e.apply_symm_apply, e.apply_symm_apply, hc])
  rwa [hP', hP', e.apply_symm_apply, e.apply_symm_apply] at this

end GlobalTheory.Ex.Arch
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

namespace GlobalTheory.Ex.Arch

theorem reframe : ThetaUnifAV → ReframeSt := by
  intro hT Q L₀ g u₀ _ _ _
  obtain ⟨rig, hrig⟩ := Q.rigid
  obtain ⟨u, Hm, χ, Ef, hAH, -, ht₁, ht₂, -, -, hEf, -⟩ := hT Q rig hrig
  obtain ⟨F, hF₀, -⟩ := HomLinear.exists_linear_of_isMonHom Q.A Q.A Q.isAb Q.isAb L₀ Q.L g Q.g u₀ u ht₁ ht₂
    (𝟙 _) inferInstance
  have hF : ∀ z, u.ex (F z) = u₀.ex z := fun z => (hF₀ z).trans (Category.comp_id _)
  have hΛ : ∀ z, F z ∈ u.Λ ↔ z ∈ u₀.Λ := fun z => by rw [← u.ker, hF, u₀.ker]
  have cΛ : (u.Λ : Set (Fin Q.g → ℂ)).Countable := by
    have := u.discrete
    exact (countable_of_Lindelof_of_discrete : Countable u.Λ)
  have cΛ₀ : (u₀.Λ : Set (Fin g → ℂ)).Countable := by
    have := u₀.discrete
    exact (countable_of_Lindelof_of_discrete : Countable u₀.Λ)
  have Finj : Function.Injective F := (injective_iff_map_eq_zero F).2 fun z hz =>
    FibreUnif.eq_zero_of_smul_mem_countable cΛ₀ fun t =>
      (hΛ _).1 (by rw [map_smul, hz, smul_zero]; exact u.Λ.zero_mem)
  have Fsurj : Function.Surjective F := FibreUnif.surjective_of_countable F cΛ fun v => by
    obtain ⟨z, hz⟩ := u₀.ex_onto (u.ex v)
    refine ⟨z, (u.ker _).1 ?_⟩
    have := u.ex_add (v - F z) (F z)
    rw [sub_add_cancel, hF, hz] at this
    exact right_eq_mul.1 this
  exact ⟨u, Hm, χ, Ef, LinearEquiv.ofBijective F ⟨Finj, Fsurj⟩, hAH, hEf, hF⟩

end GlobalTheory.Ex.Arch
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch
noncomputable section
namespace GlobalTheory.Ex.Arch

theorem int_eq_of_exp_div_eq {m n : ℤ} (h : ∀ k : ℕ, 0 < k →
    Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / k) = Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k)) :
    m = n := by
  have hd : ∀ k : ℕ, 0 < k → (k : ℤ) ∣ m - n := fun k hk => by
    obtain ⟨j, hj⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h k hk)
    have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
    have hp : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
    refine ⟨-j, ?_⟩
    have : ((m - n : ℤ) : ℂ) = ((k * -j : ℤ) : ℂ) := by
      push_cast
      apply mul_left_cancel₀ hp
      have h2 := congrArg (· * (k : ℂ)) hj
      simp only [add_mul, div_mul_cancel₀ _ hk'] at h2
      linear_combination -h2
    exact_mod_cast this
  refine sub_eq_zero.1 (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hd ((m - n).natAbs + 1) (Nat.succ_pos _)) ?_)
  rw [Int.natAbs_natCast]
  exact Nat.lt_succ_self _

theorem objSt_of_triple_reframe : Laws → TripleSt → ReframeSt → ObjSt := by
  intro laws hT hR E _ _ _ H D La _ _ EF g ty P Hm₀ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  obtain ⟨Q, oa, L₀, u₀, hg, hiso, hdet, ht₁, ht₂, hker, hact, hW⟩ :=
    hT E H D La EF g ty P Hm₀ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  obtain ⟨u, Hm, χ, Ef, F, hAH, hE, hF⟩ := hR Q L₀ g u₀ hg ht₁ ht₂
  have hΛ : ∀ a, F (P a) ∈ u.Λ := fun a => (u.ker _).1 ((hF _).trans ((hker _).2 ⟨a, rfl⟩))
  have hsur : ∀ z ∈ u.Λ, ∃ a, z = F (P a) := fun z hz => by
    obtain ⟨w, rfl⟩ := F.surjective z
    obtain ⟨a, ha⟩ := (hker w).1 ((hF w).symm.trans ((u.ker _).2 hz))
    exact ⟨a, by rw [ha]⟩
  have hW' : ∀ (k : ℕ) a b (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) →
      WeilIs Q.A Q.L k (u.ex ((k : ℂ)⁻¹ • F (P a))) (u.ex ((k : ℂ)⁻¹ • F (P b))) (unitOn c) := fun k a b c hk hc => by
    rw [← map_smul F, ← map_smul F, hF, hF]
    exact hW k a b c hk hc
  have hEf : ∀ a b, Ef ⟨F (P a), hΛ a⟩ ⟨F (P b), hΛ b⟩ = EF a b := fun a b => int_eq_of_exp_div_eq fun k hk => by
    have w₁ := PeriodPoint.weilIs_of_isAH laws Q rfl u hAH Ef hE k ⟨F (P a), hΛ a⟩ ⟨F (P b), hΛ b⟩
      (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    have w₂ := hW' k a b (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    exact congrArg Units.val
      (PrimUnif.unitOn_inj' (CommutatorPairing.weilIs_unique laws.globalFns Q.isAb Q.isLB w₁ w₂))
  have hact' : ∀ (a : 𝓞 E) z, u.ex (F fun k => ty k (a : E) * z k) = u.ex (F z) ≫ oa.act a := fun a z => by
    rw [hF, hF, hact]
  let d : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
    LinearMap.pi fun k => ty k (H.w0 : E) • LinearMap.proj (R := ℂ) (φ := fun _ => ℂ) k
  let G : (Fin Q.g → ℂ) →ₗ[ℂ] (Fin Q.g → ℂ) := F.toLinearMap ∘ₗ d ∘ₗ F.symm.toLinearMap
  have hG : ∀ z, G (F z) = F fun k => ty k (H.w0 : E) * z k := fun z => by
    change F (d (F.symm (F z))) = _
    rw [F.symm_apply_apply]
    rfl
  have hGP : ∀ a, G (F (P a)) = F (P (H.w0 • a)) := fun a => by
    rw [hG]
    congr 1
    funext k
    exact (h4 _ _ _).symm
  have hGΛ : ∀ l ∈ u.Λ, G l ∈ u.Λ := fun l hl => by
    obtain ⟨a, rfl⟩ := hsur l hl
    rw [hGP]
    exact hΛ _
  have hGex : ∀ z, u.ex (G z) = u.ex z ≫ oa.act H.w0 := fun z => by
    obtain ⟨w, rfl⟩ := F.surjective z
    rw [hG, hact']
  have hχ := (@GlobalTheory.SelfCube.appellHumbert_data_of_iso_cube GlobalTheory.valAt'_rules
    (GlobalTheory.holFamily_lift GlobalTheory.valAt'_rules) Q Q.isAb.comm u Hm χ Ef
    ⟨hAH.1, hAH.2.2.1, hE, hAH.2.2.2⟩ (oa.act H.w0) G hGΛ hGex hiso).2
  refine ⟨Q, oa, u, Hm, χ, F, hΛ, hiso, hdet, hAH, hsur, fun a b => ?_, fun a => ?_, hact', hW'⟩
  · rw [← hEf]
    exact (hE ⟨F (P a), hΛ a⟩ ⟨F (P b), hΛ b⟩).symm
  · rw [hχ, ← hEf]
    congr 2
    exact Subtype.ext (hGP a)

end GlobalTheory.Ex.Arch
end
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
noncomputable section
namespace GlobalTheory.Ex.Arch

theorem isThetaPt_classical (hL : Laws) (hL2 : Laws2) (hT : ThetaUnifAV) (P : PolAV (Sp ℂ))
    (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin P.g → ℂ) → ℂ) (N : ℕ)
    {I : Type} (x : I → (baseOver (Sp ℂ) ⟶ P.A)) (l : I → u.Λ) (hN : Odd N) (hAH : u.IsAH Hm χ)
    (hθ : u.IsThetaFn Hm χ 1 θ) (h0 : θ ≠ 0) (hx : ∀ i, x i = u.ex (((N : ℂ) ^ 2)⁻¹ • (l i : Fin P.g → ℂ))) :
    IsThetaPt P N x fun i => fnOf (χ (l i) * Complex.exp (-(Real.pi / 2 / (N : ℂ) ^ 2) * hermForm Hm (l i) (l i)) *
      θ ((N : ℂ)⁻¹ • (l i : Fin P.g → ℂ))) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.pos.ne'
  refine ⟨hN, isUnit_natCast_sp hN0, fun q => ⟨⊤, trivial, ?_⟩⟩
  let T : Over (Sp ℂ) := overRes (T := baseOver (Sp ℂ)) ⊤
  haveI : IsIso T.hom := by
    show IsIso ((⊤ : (Sp ℂ).Opens).ι ≫ 𝟙 _)
    rw [Category.comp_id]
    exact inferInstanceAs (IsIso (Sp ℂ).topIso.hom)
  let p : 𝟙_ (Over (Sp ℂ)) ⟶ T := Over.homMk (inv T.hom) (by simp)
  have hp : p ≫ overResι (T := baseOver (Sp ℂ)) ⊤ = 𝟙 _ := by
    ext1
    show inv T.hom ≫ (⊤ : (Sp ℂ).Opens).ι = 𝟙 _
    rw [IsIso.inv_comp_eq]
    rfl
  have htor : ∀ i, x i ^ (N ^ 2) = 1 := fun i => by
    rw [hx]
    refine (ThetaClassical.ex_nsmul u _ _).symm.trans ((u.ker _).2 ?_)
    rw [← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_pow, smul_inv_smul₀ (pow_ne_zero _ hN0)]
    exact (l i).2
  have key := ThetaClassical.isThetaPtOver hL hL2 hT P u Hm χ θ N T p (fun i => overResι ⊤ ≫ x i) l
    hN hAH hθ h0 (fun i => (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x i) hp).trans
      ((Category.id_comp _).trans (hx i))))
    (fun i => ThetaClassical.exists_symLift hL P (N ^ 2) _ (by push_cast; rfl) hN.pow (x i) (htor i))
  convert key using 2 with i
  exact ThetaClassical.constFn_top _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_tateIso (D : Datum H) {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (EF : LinearMap.BilinForm ℤ La)
    (Q : PolAV (Sp ℂ)) (act : 𝓞 E → (Q.A ⟶ Q.A)) (hact : ∀ c, IsMonHom (act c)) {g : ℕ} (u : HolUnif Q.A Q.L g)
    (P : La →+ (Fin g → ℂ)) (hinj : Function.Injective P) (hker : ∀ z, z ∈ u.Λ ↔ ∃ a, z = P a)
    (hlin : ∀ (c : 𝓞 E) (s : ℂ) a, u.ex (s • P (c • a)) = u.ex (s • P a) ≫ act c)
    (hW : ∀ (k : ℕ) a b (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) →
      WeilIs Q.A Q.L k (u.ex ((k : ℂ)⁻¹ • P a)) (u.ex ((k : ℂ)⁻¹ • P b)) (unitOn c))
    (ζ : ℕ → ℂˣ) (hp : ∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) (hc : ∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n)
    (f : ℕ → D.La → La) (hf : IsTower D EF ζ f) :
    ∃ I : TateIso D ℂ (baseOver (Sp ℂ) ⟶ Q.A) (fun a x => x ≫ act a) (fun n x x' c => WeilIs Q.A Q.L n x x' (unitOn c)),
      I.ζ = ζ ∧ ∀ (n : ℕ) a, I.ev n a = u.ex ((n : ℂ)⁻¹ • P (f n a)) := by
  let e : (Fin g → ℂ) → (baseOver (Sp ℂ) ⟶ Q.A) := u.ex
  have eadd : ∀ z w, e (z + w) = e z * e w := u.ex_add
  have eker : ∀ z, e z = 1 ↔ ∃ a, z = P a := fun z => (u.ker z).trans (hker z)
  have epow : ∀ z (n : ℕ), e z ^ n = e (n • z) := fun z n => (ThetaClassical.ex_nsmul u z n).symm
  have e0 : e 0 = 1 := (eker 0).2 ⟨0, (map_zero P).symm⟩
  have hn : ∀ n : ℕ, 0 < n → (n : ℂ) ≠ 0 := fun n h => Nat.cast_ne_zero.2 h.ne'
  have sm : ∀ n : ℕ, 0 < n → ∀ a, (n : ℂ)⁻¹ • P (n • a) = P a := fun n h a => by
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ (hn n h)]
  have sm' : ∀ n : ℕ, 0 < n → ∀ z : Fin g → ℂ, n • (n : ℂ)⁻¹ • z = z := fun n h z => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ (hn n h)]
  have md : ∀ n : ℕ, 0 < n → ∀ a b, e ((n : ℂ)⁻¹ • P (a + n • b)) = e ((n : ℂ)⁻¹ • P a) := fun n h a b => by
    rw [map_add, smul_add, eadd, sm n h, (eker _).2 ⟨b, rfl⟩, _root_.mul_one]
  refine ⟨{ ζ := ζ, ζ_prim := hp, ζ_pow := hc, ev := fun n a => e ((n : ℂ)⁻¹ • P (f n a)), add := fun n a b => ?_,
            lin := fun n c a => ?_, ker := fun n h a => ?_, onto := fun n h x => ⟨fun hx => ?_, ?_⟩,
            tower := fun n m h h' a => ?_, isom := fun n h a b => ?_ }, rfl, fun _ _ => rfl⟩
  · rcases n.eq_zero_or_pos with rfl | h
    · simp only [Nat.cast_zero, inv_zero, zero_smul, e0, _root_.mul_one]
    · obtain ⟨c, hc⟩ := (hf n h).1 a b
      rw [hc, md n h, map_add, smul_add, eadd]
  · rcases n.eq_zero_or_pos with rfl | h
    · haveI := hact c
      simp only [Nat.cast_zero, inv_zero, zero_smul, e0, MonObj.one_comp]
    · obtain ⟨b, hb⟩ := (hf n h).2.1 c a
      rw [hb, md n h]
      exact hlin c _ _
  · rw [← (hf n h).2.2.1 a, eker]
    refine exists_congr fun b => ⟨fun hb => hinj ?_, fun hb => by rw [hb, sm n h]⟩
    rw [map_nsmul, ← hb, sm' n h]
  · obtain ⟨z, rfl⟩ : ∃ z, e z = x := u.ex_onto x
    rw [epow, eker] at hx
    obtain ⟨b, hb⟩ := hx
    obtain ⟨a, c, rfl⟩ := (hf n h).2.2.2.1 b
    refine ⟨a, ?_⟩
    rw [← md n h _ c, ← hb, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ (hn n h)]
  · rintro ⟨a, rfl⟩
    rw [epow, sm' n h]
    exact (eker _).2 ⟨_, rfl⟩
  · obtain ⟨b, hb⟩ := (hf n h).2.2.2.2.1 m h' a
    rw [epow, hb, Nat.cast_mul, mul_inv, mul_comm, mul_smul, sm' m h', md n h]
  · exact hW n _ _ _ h ((hf n h).2.2.2.2.2 a b)

theorem exists_log (T : ℝ) (u : ℂˣ) (hu : ‖(u : ℂ)‖ < Real.exp (-(2 * Real.pi * T))) :
    ∃ w : ℂ, T < w.im ∧ (u : ℂ) = eTwoPi w := by
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have e : (u : ℂ) = eTwoPi (Complex.log u / (2 * Real.pi * Complex.I)) := by
    rw [eTwoPi, mul_div_cancel₀ _ h2, Complex.exp_log u.ne_zero]
  refine ⟨_, ?_, e⟩
  generalize Complex.log u / (2 * Real.pi * Complex.I) = w at e
  rw [e, eTwoPi, Complex.norm_exp, Real.exp_lt_exp] at hu
  simp at hu
  have := Real.pi_pos
  nlinarith

theorem of_steps (hL : Laws) (hL2 : Laws2) (hT : ThetaUnifAV) (hdict : DictSt) (htow : TowerSt) (hty : TypeSt)
    (hobj : ObjSt) (hth : ThetaSt) (htx : TxSt) : AllD fun {_} _ _ _ {H} D => ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (A : ArcF D R ℂ), A.ρ = H.rt0 → ∀ (k : ℕ) (β : A.N.Form k), A.Bal β → ∀ (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂˣ, ‖(u : ℂ)‖ < ε → (∀ x, Summable fun χ => ‖(A.N.twist β u).txT m (A.N.twQ β u hm (A.q _ x)) χ‖) ∧ ∃ o : Full D ℂ, o.ρ = H.rt0 ∧ o.I.ζ (m ^ 2) = A.I.ζ (m ^ 2) ∧ o.Theta m fun x => (A.N.twist β u).tx m (A.N.twQ β u hm (A.q _ x)) := by
  intro E _ _ _ H D R _ _ _ A hρ k β hβ m hm hodd
  letI := H.starRing
  obtain ⟨B, d, hact, hbe, hprim, hth0, hsig⟩ := hdict E H D R A k β hβ
  obtain ⟨f, hf, hrep⟩ := htow E H D R A B d hact
  obtain ⟨g, ty, h, htyp, hh⟩ := hty E H D B (hρ ▸ hsig)
  obtain ⟨-, hbij, hadj, T₁, hT₁⟩ := B.periods_polarised
  obtain ⟨T₂, hT₂⟩ := B.exists_convergence
  have hmem : d.th ∈ B.Theta 1 0 := d.ab.2.2.2.2.2.2.2.1
  obtain ⟨-, hsum, -, hdiff, -⟩ := hT₂ 1 0 d.th hmem
  refine ⟨Real.exp (-(2 * Real.pi * max T₁ T₂)), Real.exp_pos _, fun u hu => ?_⟩
  obtain ⟨w, hw, huw⟩ := exists_log _ u hu
  have hw₁ : T₁ < w.im := (le_max_left _ _).trans_lt hw
  have hw₂ : T₂ < w.im := (le_max_right _ _).trans_lt hw
  have hm2 : 0 < m ^ 2 := pow_pos hodd.pos 2
  have hterm := fun x => htx (𝓞 E) A.N B d H.w0 hprim k β hbe m hm hodd w u huw _ _ (hrep _ hm2 x)
  refine ⟨fun x => ?_, ?_⟩
  · refine (d.eX.toEquiv.summable_iff (f := fun χ : A.N.X => ‖(A.N.twist β u).txT m (A.N.twQ β u hm (A.q _ x)) χ‖)).1 ?_
    exact ((hsum w hw₂ ((m : ℂ)⁻¹ • B.Pw w (f (m ^ 2) x))).mul_left _).congr fun y =>
      (norm_mul _ _).symm.trans (congrArg norm (hterm x y).symm)
  obtain ⟨-, -, hlin, -, hspan, -, -, -, hper⟩ := hT₁ w hw₁
  let P : B.La →+ (Fin g → ℂ) := h.toLinearMap.toAddMonoidHom.comp (B.Pw w)
  obtain ⟨hinj, hdisc, hsp, Hm, hherm, hpos, him⟩ := hper g h P fun _ => rfl
  have hPlin : ∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i := fun a x i =>
    (congrArg (fun v => h v i) (hlin a x)).trans (hh a _ i)
  obtain ⟨Q, oa, U, Hm', χ, F, hΛ, hpr, hdet, hAH, hΛ', him', hχ, hex, hW⟩ :=
    hobj E H D B.La B.EF g ty P Hm htyp hbij hadj hPlin hinj hdisc hsp hherm hpos him
  let P' : B.La →+ (Fin Q.g → ℂ) := F.toLinearMap.toAddMonoidHom.comp P
  obtain ⟨I, hI, hev⟩ := exists_tateIso D B.EF Q oa.act oa.hom U P' (F.injective.comp hinj)
    (fun z => ⟨hΛ' z, fun ⟨a, ha⟩ => ha ▸ hΛ a⟩) (fun c s a => by
      have := hex c (s • P a)
      rw [map_smul] at this
      refine Eq.trans (congrArg U.ex ?_) this
      refine (map_smul F s _).symm.trans (congrArg F (funext fun i => ?_))
      simp only [Pi.smul_apply, hPlin, smul_eq_mul]
      ring) hW A.I.ζ A.I.ζ_prim A.I.ζ_pow f hf
  have hS : Differentiable ℂ (B.Sum 1 0 d.th w) := fun v =>
    ((hdiff.differentiableAt ((isOpen_lt continuous_const (Complex.continuous_im.comp continuous_fst)).mem_nhds
      (show T₂ < ((w, v) : ℂ × B.V).1.im from hw₂))).comp v
      ((differentiableAt_const w).prodMk differentiableAt_id) :)
  obtain ⟨Θ, hΘ, hΘ0, hΘp, hΘv⟩ := hth (𝓞 E) B H.w0 hprim d.th hmem w hS Q.g (h.trans F) Hm' hAH.1 hspan him'
  have hne : Θ ≠ 0 := by
    obtain ⟨v, hv⟩ := B.exists_Sum_ne_zero one_ne_zero 0 hth0 (w := w) fun z => (hsum w hw₂ _).of_norm
    exact fun e => hv ((hΘ0 v).1 (congrFun e _))
  have hfn : U.IsThetaFn Hm' χ 1 Θ := ⟨hΘ, fun l z => by
    obtain ⟨l, hl⟩ := l
    obtain ⟨a, rfl⟩ := hΛ' l hl
    rw [pow_one, hχ]
    exact hΘp a z⟩
  refine ⟨⟨Q, oa, hpr, H.rt0, H.sqrt_neg_disc_sq, hdet, I, inferInstance⟩, rfl, congrFun hI _, ?_⟩
  have key := isThetaPt_classical hL hL2 hT Q U Hm' χ Θ m (I.ev (m ^ 2)) (fun x => ⟨F (P (f _ x)), hΛ _⟩) hodd hAH hfn hne
    fun x => by rw [hev, Nat.cast_pow]; rfl
  refine Eq.mp (congrArg (IsThetaPt Q m (I.ev (m ^ 2))) (funext fun x => congrArg fnOf ?_)) key
  rw [hχ, _root_.mul_assoc]
  refine (congrArg (_ * ·) (hΘv _ m hodd.pos.ne')).trans ?_
  rw [← _root_.mul_assoc, AnArc.Sum, ← tsum_mul_left]
  exact (tsum_congr fun y => (hterm x y).symm).trans
    (d.eX.toEquiv.tsum_eq fun χ : A.N.X => (A.N.twist β u).txT m (A.N.twQ β u hm (A.q _ x)) χ)

theorem exists_full_of_small : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllD fun {_} _ _ _ {H} D => ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (A : ArcF D R ℂ), A.ρ = H.rt0 → ∀ (k : ℕ) (β : A.N.Form k), A.Bal β → ∀ (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂˣ, ‖(u : ℂ)‖ < ε → (∀ x, Summable fun χ => ‖(A.N.twist β u).txT m (A.N.twQ β u hm (A.q _ x)) χ‖) ∧ ∃ o : Full D ℂ, o.ρ = H.rt0 ∧ o.I.ζ (m ^ 2) = A.I.ζ (m ^ 2) ∧ o.Theta m fun x => (A.N.twist β u).tx m (A.N.twQ β u hm (A.q _ x)) := fun hV _ _ _ _ _ hT =>
  have hL : Laws := hV.1.1
  have hL2 : Laws2 := hV.1.2.1
  have hF : BrFamSt := _root_.GlobalTheory.Ex.brFam hL hL2
  of_steps hL hL2 hT
    (_root_.GlobalTheory.Ex.Arch.dict_of_val (_root_.GlobalTheory.ActValues.brAct hL) (_root_.GlobalTheory.Ex.Arch.AbVal.valSt hL hF (_root_.GlobalTheory.Ex.Arch.FibEx.fibEx hL hT) _root_.GlobalTheory.Ex.Arch.fibGrp (_root_.GlobalTheory.Ex.Arch.fibCubeSt hL) (_root_.GlobalTheory.Ex.Arch.FibSym.fibSymSt hL)
      (_root_.GlobalTheory.Ex.Arch.FibRos.fibRosSt hL) (_root_.GlobalTheory.Ex.Arch.FibPrim.fibPrim_of_laws hL) _root_.GlobalTheory.Ex.Arch.fibSec (_root_.GlobalTheory.Ex.Arch.fibLie_of_laws hL)))
    (_root_.GlobalTheory.Ex.Arch.towerSt_of _root_.GlobalTheory.Ex.GtValues.points_correspond (_root_.GlobalTheory.WeilValues.weil_eq_values _root_.GlobalTheory.Ex.GtValues.points_correspond hF) _root_.GlobalTheory.Ex.Arch.ptSt (_root_.GlobalTheory.Ex.Arch.qkSt_of_ptSt _root_.GlobalTheory.Ex.Arch.ptSt) _root_.GlobalTheory.Ex.Arch.Wp.wp_eq)
    _root_.GlobalTheory.Ex.Arch.typeSt (_root_.GlobalTheory.Ex.Arch.objSt_of_triple_reframe hL (_root_.GlobalTheory.Ex.Arch.tripleSt_of_laws hL hT) (_root_.GlobalTheory.Ex.Arch.reframe hT)) _root_.GlobalTheory.Ex.Arch.theta_sum_appellHumbert (_root_.GlobalTheory.Ex.Arch.txSt_of_ptSt _root_.GlobalTheory.Ex.Arch.ptSt)

end GlobalTheory.Ex.Arch
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaPoint_complexDegeneration_small : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllD fun {_} _ _ _ {H} D => ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (A : ArcF D R ℂ), A.ρ = H.rt0 → ∀ (k : ℕ) (β : A.N.Form k), A.Bal β → ∀ (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂˣ, ‖(u : ℂ)‖ < ε → (∀ x, Summable fun χ => ‖(A.N.twist β u).txT m (A.N.twQ β u hm (A.q _ x)) χ‖) ∧ ∃ o : Full D ℂ, o.ρ = H.rt0 ∧ o.I.ζ (m ^ 2) = A.I.ζ (m ^ 2) ∧ o.Theta m fun x => (A.N.twist β u).tx m (A.N.twQ β u hm (A.q _ x)) := by
  atlas_forward_decl GlobalTheory.Ex.Arch.exists_full_of_small
end
