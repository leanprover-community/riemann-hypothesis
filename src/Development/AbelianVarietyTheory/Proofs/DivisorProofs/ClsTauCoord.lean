import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauCoordMulSq
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

section
open GlobalTheory.Poinc Matrix

namespace GlobalTheory.Poinc

open Matrix in
private lemma exists_nat_mul_rat_eq_int' {s : ℕ} (q : Fin s → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∃ n : Fin s → ℤ, ∀ u, (N : ℚ) * q u = n u := by
  refine ⟨∏ v, (q v).den, Finset.prod_pos fun v _ => (q v).den_pos,
    fun u => (q u).num * ∏ v ∈ Finset.univ.erase u, ((q v).den : ℤ), fun u => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ (fun v => (q v).den) (Finset.mem_univ u)]
  push_cast
  rw [← Rat.mul_den_eq_num (q u)]
  ring

open Matrix in
private lemma bilinForm_sum_zsmul_eq_sum_mul {s : ℕ} {X : Type} [AddCommGroup X]
    (β : LinearMap.BilinForm ℤ X) (y : Fin s → X) (n : Fin s → ℤ) :
    β (∑ u, n u • y u) (∑ v, n v • y v) = ∑ u, ∑ v, n u * n v * β (y u) (y v) := by
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  ring

open Matrix in
private lemma gram_quadratic_real_nonneg {s : ℕ} {X : Type} [AddCommGroup X]
    (β : LinearMap.BilinForm ℤ X) (hpos : ∀ x, 0 ≤ β x x) (y : Fin s → X) (c : Fin s → ℝ) :
    0 ≤ ∑ u, ∑ v, c u * c v * ((β (y u) (y v) : ℤ) : ℝ) := by
  have hdense : DenseRange (Pi.map fun _ : Fin s => (Rat.cast : ℚ → ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  refine hdense.induction_on (p := fun c : Fin s → ℝ =>
    0 ≤ ∑ u, ∑ v, c u * c v * ((β (y u) (y v) : ℤ) : ℝ)) c
    (isClosed_le continuous_const (by fun_prop)) fun q => ?_
  obtain ⟨N, hN, n, hn⟩ := exists_nat_mul_rat_eq_int' q
  have hnR : ∀ u, (N : ℝ) * (q u : ℝ) = (n u : ℝ) := fun u => by exact_mod_cast hn u
  have hNpos : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have key : (N : ℝ) ^ 2 * ∑ u, ∑ v, (q u : ℝ) * (q v : ℝ) * ((β (y u) (y v) : ℤ) : ℝ) =
      ((β (∑ u, n u • y u) (∑ v, n v • y v) : ℤ) : ℝ) := by
    rw [bilinForm_sum_zsmul_eq_sum_mul]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← hnR u, ← hnR v]
    ring
  have h0 : (0 : ℝ) ≤ ((β (∑ u, n u • y u) (∑ v, n v • y v) : ℤ) : ℝ) := by
    exact_mod_cast hpos _
  rw [← key] at h0
  exact (mul_nonneg_iff_of_pos_left hNpos).mp h0

open Matrix in

theorem _root_.GlobalTheory.Poinc.qW_nonneg_of_posW : ∀ {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ),
    _root_.GlobalTheory.Poinc.PosW W → ∀ {X : Type} [AddCommGroup X]
    (β : LinearMap.BilinForm ℤ X), (∀ a b, β a b = β b a) → (∀ x, 0 ≤ β x x) →
    ∀ y : Fin s → X, 0 ≤ _root_.GlobalTheory.Poinc.qW W β y := by
  intro s W hW X _ β hsymm hpos y
  unfold _root_.GlobalTheory.Poinc.PosW at hW
  unfold _root_.GlobalTheory.Poinc.qW
  obtain ⟨m, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hW.posSemidef
  set S : ℤ := ∑ u, ∑ w, W u w * β (y u) (y w) with hS
  have hswap : ∑ u, ∑ w, W w u * β (y u) (y w) = S := by
    rw [hS, Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => ?_
    rw [hsymm]
  have htwo : ((2 * S : ℤ) : ℝ) = ∑ u, ∑ w,
      ((W + W.transpose).map (Int.cast : ℤ → ℝ)) u w * ((β (y u) (y w) : ℤ) : ℝ) := by
    have : (2 * S : ℤ) = ∑ u, ∑ w, (W u w + W w u) * β (y u) (y w) := by
      simp only [add_mul, Finset.sum_add_distrib, hswap, hS]
      ring
    rw [this]
    push_cast
    simp [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply]
  have hnonneg : (0 : ℝ) ≤ ∑ u, ∑ w,
      ((W + W.transpose).map (Int.cast : ℤ → ℝ)) u w * ((β (y u) (y w) : ℤ) : ℝ) := by
    rw [hv]
    have e : ∀ u w, (∑ i, vecMulVec (v i) (star (v i))) u w * ((β (y u) (y w) : ℤ) : ℝ) =
        ∑ i, v i u * v i w * ((β (y u) (y w) : ℤ) : ℝ) := by
      intro u w
      simp [Matrix.sum_apply, Matrix.vecMulVec_apply, Finset.sum_mul]
    simp_rw [e]
    calc (0 : ℝ) ≤ ∑ i, ∑ u, ∑ w, v i u * v i w * ((β (y u) (y w) : ℤ) : ℝ) :=
          Finset.sum_nonneg fun i _ => gram_quadratic_real_nonneg β hpos y (v i)
      _ = ∑ u, ∑ i, ∑ w, v i u * v i w * ((β (y u) (y w) : ℤ) : ℝ) := Finset.sum_comm
      _ = ∑ u, ∑ w, ∑ i, v i u * v i w * ((β (y u) (y w) : ℤ) : ℝ) :=
          Finset.sum_congr rfl fun u _ => Finset.sum_comm
  rw [← htwo] at hnonneg
  have : (0 : ℝ) ≤ (S : ℝ) := by push_cast at hnonneg; linarith
  exact_mod_cast this

end GlobalTheory.Poinc
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.E8Order

open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues

variable {R : Type} [CommRing R] [IsDomain R]

abbrev unitsR (R : Type) [CommRing R] [IsDomain R] : Subgroup (FractionRing R)ˣ :=
  (Units.map (algebraMap R (FractionRing R)).toMonoidHom).range

abbrev QR (R : Type) [CommRing R] [IsDomain R] := (FractionRing R)ˣ ⧸ unitsR R

abbrev cls : (FractionRing R)ˣ →* QR R := QuotientGroup.mk' (unitsR R)

theorem cls_eq_iff (x y : (FractionRing R)ˣ) :
    cls x = cls y ↔ ∃ u : Rˣ, (x : FractionRing R) = (y : FractionRing R) * algebraMap R (FractionRing R) u := by
  rw [eq_comm, QuotientGroup.mk'_eq_mk']
  constructor
  · rintro ⟨z, ⟨u, rfl⟩, hz⟩
    exact ⟨u, by rw [← hz]; rfl⟩
  · rintro ⟨u, hu⟩
    exact ⟨_, ⟨u, rfl⟩, Units.ext (by rw [hu]; rfl)⟩

theorem cls_unit (u : Rˣ) : cls (Units.map (algebraMap R (FractionRing R)).toMonoidHom u) = 1 :=
  (QuotientGroup.eq_one_iff _).2 ⟨u, rfl⟩

variable [IsLocalRing R]

def tq (D : DegPre R) (a b : D.X) : QR R :=
  cls (psiCoord D (a + b)) * (cls (psiCoord D a))⁻¹ * (cls (psiCoord D b))⁻¹

theorem cls_tauCoord {D : DegPre R} {a b : D.X} {x : (FractionRing R)ˣ} (hx : IsTauCoord D a b x) :
    cls x = tq D a b := by
  obtain ⟨u, hu⟩ := GlobalTheory.TauCoordQuot.main R D a b x _ _ _ hx (psiCoord_spec D (a + b)) (psiCoord_spec D a)
    (psiCoord_spec D b)
  have : x = Units.map (algebraMap R (FractionRing R)).toMonoidHom u *
      (psiCoord D (a + b) * (psiCoord D a)⁻¹ * (psiCoord D b)⁻¹) := by
    ext; rw [hu]; simp <;> ring
  rw [this, map_mul, cls_unit, _root_.one_mul, tq, map_mul, map_mul, map_inv, map_inv]

theorem tq_symm (D : DegPre R) (a b : D.X) : tq D a b = tq D b a := by
  simp only [tq, add_comm a b]; exact mul_right_comm _ _ _

theorem tq_add_left (D : DegPre R) (hB : D.TauBimult) (a z b : D.X) : tq D (a + z) b = tq D a b * tq D z b := by
  obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D a b
  obtain ⟨x', hx'⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D z b
  obtain ⟨x'', hx''⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D (a + (1 : ℕ) • z) b
  obtain ⟨u, hu⟩ := GlobalTheory.TauShift.main R D hB a z b 1 x x' x'' hx hx' hx''
  rw [one_smul] at hx''
  rw [← cls_tauCoord hx'', ← cls_tauCoord hx, ← cls_tauCoord hx', hu, map_mul, cls_unit, _root_.one_mul, pow_one, map_mul]

def tqHom (D : DegPre R) (hB : D.TauBimult) (a : D.X) : D.X →+ Additive (QR R) :=
  AddMonoidHom.mk' (fun b => Additive.ofMul (tq D a b)) fun b b' => by
    rw [tq_symm D a (b + b'), tq_add_left D hB, tq_symm D b a, tq_symm D b' a]; rfl

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsDiscreteValuationRing R → ∀ (D D' : DegPre R), D'.TauBimult → D'.PsiEven → D.TauBimult → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (ϖ : R) (β : LinearMap.BilinForm ℤ D.X), (∀ a b, β a b = β b a) → (∀ a, 0 ≤ β a a) → (∀ a b' (x : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D a b' x → ∃ u : Rˣ, (x : FractionRing R) = algebraMap R (FractionRing R) (u : R) * algebraMap R (FractionRing R) ϖ ^ (β a b')) → ∀ (c : Fin 8 → (D.X →+ D'.X)) (e : D'.X ≃+ (Fin 8 → D.X)), (∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y) → (∀ v a' b (x x' : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D (e a' v) b x → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D' a' (c v b) x' → ∃ u : Rˣ, (x : FractionRing R) = algebraMap R (FractionRing R) (u : R) * (x' : FractionRing R)) → ∀ y r, PsiCoord D' y r → 0 ≤ qW W β (e y) ∧ Associated r (ϖ ^ (qW W β (e y)).toNat) := by
  intro R _ _ _ hR D D' hB' hE' hB W hW ϖ β hs hp hτ c e hsum hcomp y r hr
  haveI := hR
  have hq : 0 ≤ qW W β (e y) := GlobalTheory.Poinc.qW_nonneg_of_posW W hW.1 β hs hp (e y)
  refine ⟨hq, ?_⟩
  obtain ⟨s, hsd⟩ : ∃ s, s = e y := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : Fin 8 → D.X, t = fun v => ∑ u, (W + W.transpose) v u • s u := ⟨_, rfl⟩
  rw [← hsd] at hq ⊢
  have hsum2 : ∑ v, β (s v) (-(t v)) = -(2 * qW W β s) := by
    subst ht
    simp only [map_neg, map_sum, map_zsmul, smul_eq_mul, Finset.sum_neg_distrib, neg_inj]
    simp only [Matrix.add_apply, Matrix.transpose_apply, add_mul, Finset.sum_add_distrib, qW, two_mul]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by rw [hs]
  have h1 : ∑ v, c v (t v) = y := by rw [ht, hsd]; exact hsum y
  have hy : -y = ∑ v, c v (-(t v)) := by
    rw [← h1]; simp only [map_neg, Finset.sum_neg_distrib]
  obtain ⟨x', hx'⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D' y (-y)
  have hcl : cls x' = tq D' y (-y) := cls_tauCoord hx'
  have hterm : ∀ v, tq D' y (c v (-(t v))) = tq D (s v) (-(t v)) := by
    intro v
    obtain ⟨a, ha⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D (e y v) (-(t v))
    obtain ⟨b, hb⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D' y (c v (-(t v)))
    obtain ⟨u, hu⟩ := hcomp v y (-(t v)) a b ha hb
    rw [← cls_tauCoord hb, hsd, ← cls_tauCoord ha]
    exact ((cls_eq_iff _ _).2 ⟨u, by rw [hu, mul_comm]⟩).symm
  have hprod : Additive.ofMul (tq D' y (-y)) = ∑ v, Additive.ofMul (tq D (s v) (-(t v))) := by
    have := map_sum (tqHom D' hB' y) (fun v => c v (-(t v))) Finset.univ
    rw [← hy] at this
    refine this.trans ?_
    exact Finset.sum_congr rfl fun v _ => congrArg Additive.ofMul (hterm v)
  obtain ⟨w0, hw0⟩ := GlobalTheory.PsiFromTauEven.tauCoord_mul_sq R D' hB' hE' y r hr x' hx'
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_pow two_ne_zero, mul_zero] at hw0
    exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 w0.ne_zero hw0.symm
  let ru : (FractionRing R)ˣ := toUnitK r hr0
  have hru : x' * ru ^ 2 = Units.map (algebraMap R (FractionRing R)).toMonoidHom w0 := by
    ext; simp [ru, toUnitK, hw0]
  have hcr : cls ru ^ 2 = (cls x')⁻¹ := by
    have := congrArg cls hru
    rw [map_mul, map_pow, cls_unit] at this
    exact eq_inv_of_mul_eq_one_right this
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hq
  rw [hn, Int.toNat_natCast]
  have final : ∀ ρ : (FractionRing R)ˣ, (ρ : FractionRing R) = algebraMap R (FractionRing R) (ϖ ^ n) →
      cls ru ^ 2 = cls ρ ^ 2 → Associated r (ϖ ^ n) := by
    intro ρ hρ h
    rw [← map_pow, ← map_pow] at h
    obtain ⟨u, hu⟩ := (cls_eq_iff _ _).1 h
    simp only [Units.val_pow_eq_pow_val, hρ, ru, toUnitK, Units.val_mk0, ← map_pow, ← map_mul] at hu
    have hsq : Associated ((ϖ ^ n) ^ 2) (r ^ 2) := ⟨u, (IsFractionRing.injective R (FractionRing R) hu).symm⟩
    exact (associated_of_dvd_dvd ((IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1 hsq.dvd)
      ((IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1 hsq.symm.dvd)).symm
  by_cases hϖ : ϖ = 0
  · have hβ0 : ∀ a b, β a b = 0 := by
      intro a b
      obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D a b
      obtain ⟨u, hu⟩ := hτ a b x hx
      by_contra h
      rw [hϖ, map_zero, zero_zpow _ h, mul_zero] at hu
      exact x.ne_zero hu
    have hq0 : qW W β s = 0 := by simp [qW, hβ0]
    have htq : ∀ a b, tq D a b = 1 := by
      intro a b
      obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D a b
      obtain ⟨u, hu⟩ := hτ a b x hx
      rw [← cls_tauCoord hx]
      have : x = Units.map (algebraMap R (FractionRing R)).toMonoidHom u := by
        ext; rw [hu, hβ0, zpow_zero, _root_.mul_one]; rfl
      rw [this, cls_unit]
    have h1' : tq D' y (-y) = 1 := by
      apply Additive.ofMul.injective
      rw [hprod]; simp [htq]
    have hn0 : n = 0 := by omega
    subst hn0
    refine final 1 (by simp) ?_
    rw [hcr, hcl, h1']; simp
  · let ϖu : (FractionRing R)ˣ := toUnitK ϖ hϖ
    have htq : ∀ a b, tq D a b = cls ϖu ^ β a b := by
      intro a b
      obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D a b
      obtain ⟨u, hu⟩ := hτ a b x hx
      rw [← cls_tauCoord hx, ← map_zpow]
      exact (cls_eq_iff _ _).2 ⟨u, by rw [hu, Units.val_zpow_eq_zpow_val]; simp [ϖu, toUnitK, mul_comm]⟩
    have hx'cl : cls x' = cls ϖu ^ (-(2 * qW W β s)) := by
      rw [hcl]; apply Additive.ofMul.injective; rw [hprod]
      simp only [htq, ofMul_zpow]
      rw [← Finset.sum_smul, hsum2]
    refine final (ϖu ^ n) (by simp [ϖu, toUnitK]) ?_
    rw [hcr, hx'cl, hn, map_pow, ← zpow_neg, neg_neg, show (2 * (n : ℤ)) = ((n * 2 : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast, pow_mul]

end GlobalTheory.Poinc.E8Order
end
end
