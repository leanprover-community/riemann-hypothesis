import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinTypInvariantFormOfIsotIn
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosets
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryAdmissibleMatrixCoefficient
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmFieldAdeleSplitPlaceSupportIntegral
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegerUnitSplitPlaceConjugatePrime
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionRealSubfieldRingEquiv

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.IrrSplitSub

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem commute_of_trivOutside (s : SplitPlace L) {x y : GAf L n} (hx : TrivOutside {s.v} x)
    (hy : TrivOutside {s.v}ᶜ y) : x * y = y * x := by
  apply Subtype.ext; apply Units.ext
  show (x.1 : Matrix (Fin n) (Fin n) (AL L)) * y.1 = (y.1 : Matrix (Fin n) (Fin n) (AL L)) * x.1
  ext i j
  rw [← sub_eq_zero]
  apply GlobalTheory.InertUmax.eq_zero_of_compAt L
  intro w
  rw [map_sub, sub_eq_zero]
  have hmx : ∀ A B : Matrix (Fin n) (Fin n) (AL L),
      compAt L w ((A * B) i j) = (A.map (compAt L w) * B.map (compAt L w)) i j := by
    intro A B; rw [← Matrix.map_mul]; rfl
  rw [hmx, hmx]
  by_cases hw : w = s.v
  · rw [hy w (by simp [hw]), mul_one, one_mul]
  · rw [hx w (by simpa using hw), mul_one, one_mul]

theorem cong_conj {N : ℕ} {a k : GAf L n} (ha : a ∈ Umax L n) (hk : NG.Cong L n N k) :
    NG.Cong L n N (a⁻¹ * k * a) := by
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) hk.1) ha, ?_⟩
  choose Y hY hYe using hk.2
  let Ym : Matrix (Fin n) (Fin n) (AL L) := Matrix.of Y
  have hint : ∀ A B : Matrix (Fin n) (Fin n) (AL L), (∀ i j, A i j ∈ ALint L) → (∀ i j, B i j ∈ ALint L) →
      ∀ i j, (A * B) i j ∈ ALint L := fun A B hA hB i j => by
    rw [Matrix.mul_apply]; exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hA i l) (hB l j)
  have haI : ∀ i j, ((a.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := ha
  have haiI : ∀ i j, (((a⁻¹).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L :=
    Subgroup.inv_mem _ ha
  have hAiA : (((a⁻¹).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      ((a.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  have hK : ((k.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) - 1 = (N : AL L) • Ym := by
    ext i j; simp [Ym, hYe i j]
  have hmat : (((a⁻¹ * k * a).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) - 1 =
      (N : AL L) • ((((a⁻¹).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) * Ym *
        ((a.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))) := by
    have e : (((a⁻¹ * k * a).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (((a⁻¹).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
          ((k.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
          ((a.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) := rfl
    rw [e]
    calc _ = (((a⁻¹).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
          ((k.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
          ((a.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) -
          (((a⁻¹).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) * 1 *
          ((a.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) := by rw [Matrix.mul_one, hAiA]
      _ = (((a⁻¹).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
          (((k.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) - 1) *
          ((a.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) := by
        rw [Matrix.mul_sub, Matrix.sub_mul]
      _ = _ := by rw [hK, Matrix.mul_smul, Matrix.smul_mul]
  intro i j
  refine ⟨_, hint _ _ (hint _ _ haiI (fun i j => hY i j)) haI i j, ?_⟩
  have := congrFun (congrFun hmat i) j
  rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at this
  exact this

theorem cong_factor (s : SplitPlace L) (N : ℕ) (κ : GAf L n) (hκ : NG.Cong L n N κ) :
    ∃ x y : GAf L n, TrivOutside {s.v} x ∧ NG.Cong L n N x ∧ TrivOutside {s.v}ᶜ y ∧ NG.Cong L n N y ∧
      κ = x * y := by
  classical
  set e : AL L := (1 : L) ⊗ₜ[maximalRealSubfield L] GlobalTheory.InertUmax.sgl L s.v 1 with he_def
  have hsgl : GlobalTheory.InertUmax.sgl L s.v 1 * GlobalTheory.InertUmax.sgl L s.v 1 = GlobalTheory.InertUmax.sgl L s.v 1 := by
    refine RestrictedProduct.ext _ _ fun w => ?_
    change GlobalTheory.InertUmax.sgl L s.v 1 w * GlobalTheory.InertUmax.sgl L s.v 1 w = GlobalTheory.InertUmax.sgl L s.v 1 w
    rcases eq_or_ne w s.v with rfl | hw
    · simp only [GlobalTheory.InertUmax.sgl_same, mul_one]
    · simp only [GlobalTheory.InertUmax.sgl_ne L _ _ hw, mul_zero]
  have he2 : e * e = e := by rw [he_def, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hsgl]
  have hce : conjAL L e = e := by simp [he_def, conjAL, Algebra.TensorProduct.map_tmul]
  have heI : e ∈ ALint L := GlobalTheory.InertUmax.one_tmul_sgl_mem L s.v 1 (one_mem _)
  have hcv : compAt L s.v e = 1 := by
    rw [he_def, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_same]; rfl
  have hcw : ∀ w, w ≠ s.v → compAt L w e = 0 := fun w hw => by
    rw [he_def, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_ne L _ _ hw, TensorProduct.tmul_zero]
  let θ : AL L × AL L →+* AL L :=
    { toFun := fun q => e * q.1 + (1 - e) * q.2
      map_one' := by simp only [Prod.fst_one, Prod.snd_one]; ring
      map_mul' := fun q q' => by
        simp only [Prod.fst_mul, Prod.snd_mul]
        linear_combination (-(q.1 * q'.1 - q.1 * q'.2 - q.2 * q'.1 + q.2 * q'.2)) * he2
      map_zero' := by simp
      map_add' := fun q q' => by simp only [Prod.fst_add, Prod.snd_add]; ring }
  have hθ : ∀ q, θ q = e * q.1 + (1 - e) * q.2 := fun _ => rfl
  have hθc : ∀ a b, conjAL L (θ (a, b)) = θ (conjAL L a, conjAL L b) := by
    intro a b; rw [hθ, hθ, map_add, map_mul, map_mul, map_sub, map_one, hce]
  have hθv : ∀ q, compAt L s.v (θ q) = compAt L s.v q.1 := by
    intro q; rw [hθ, map_add, map_mul, map_mul, map_sub, map_one, hcv]; ring
  have hθw : ∀ w, w ≠ s.v → ∀ q, compAt L w (θ q) = compAt L w q.2 := by
    intro w hw q; rw [hθ, map_add, map_mul, map_mul, map_sub, map_one, hcw w hw]; ring
  let pr : Matrix (Fin n) (Fin n) (AL L) → Matrix (Fin n) (Fin n) (AL L) → Matrix (Fin n) (Fin n) (AL L × AL L) :=
    fun A B i j => (A i j, B i j)
  have pr_mul : ∀ A B C D, pr A B * pr C D = pr (A * C) (B * D) := by
    intro A B C D; ext i j
    · show (∑ l, pr A B i l * pr C D l j).1 = ∑ l, A i l * C l j
      rw [Prod.fst_sum]; rfl
    · show (∑ l, pr A B i l * pr C D l j).2 = ∑ l, B i l * D l j
      rw [Prod.snd_sum]; rfl
  have pr_one : pr 1 1 = 1 := by
    ext i j <;> by_cases h : i = j <;> simp [pr, Matrix.one_apply, h]
  let M : Matrix (Fin n) (Fin n) (AL L) → Matrix (Fin n) (Fin n) (AL L) → Matrix (Fin n) (Fin n) (AL L) :=
    fun A B => (pr A B).map θ
  have hM : ∀ A B i j, M A B i j = e * A i j + (1 - e) * B i j := fun _ _ _ _ => rfl
  have M_mul : ∀ A B C D, M A B * M C D = M (A * C) (B * D) := by
    intro A B C D; show (pr A B).map θ * (pr C D).map θ = (pr (A * C) (B * D)).map θ
    rw [← Matrix.map_mul, pr_mul]
  have M_one : M 1 1 = 1 := by
    show (pr 1 1).map θ = 1
    rw [pr_one, Matrix.map_one _ (map_zero θ) (map_one θ)]
  have M_conj : ∀ A B, conjT (conjAL L) (M A B) = M (conjT (conjAL L) A) (conjT (conjAL L) B) := by
    intro A B; ext i j
    show conjAL L (θ (A j i, B j i)) = θ (conjAL L (A j i), conjAL L (B j i))
    exact hθc _ _
  have M_diag : ∀ A, M A A = A := by intro A; ext i j; rw [hM]; ring
  set K : Matrix (Fin n) (Fin n) (AL L) := ((κ.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) with hK
  have hKK : K * conjT (conjAL L) K = 1 := κ.2
  have hKI : ∀ i j, K i j ∈ ALint L := hκ.1
  have h1I : ∀ i j, (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := by
    intro i j; rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hX : M K 1 * conjT (conjAL L) (M K 1) = 1 := by
    rw [M_conj, M_mul, hKK, conjT_one, Matrix.mul_one, M_one]
  have hY : M 1 K * conjT (conjAL L) (M 1 K) = 1 := by
    rw [M_conj, M_mul, hKK, conjT_one, Matrix.mul_one, M_one]
  let gX : GL (Fin n) (AL L) := ⟨M K 1, conjT (conjAL L) (M K 1), hX, mul_eq_one_comm.mp hX⟩
  let gY : GL (Fin n) (AL L) := ⟨M 1 K, conjT (conjAL L) (M 1 K), hY, mul_eq_one_comm.mp hY⟩
  have hc1 : ∀ w i j, compAt L w ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) = (1 : Matrix (Fin n) (Fin n) _) i j := by
    intro w i j; rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
  refine ⟨⟨gX, hX⟩, ⟨gY, hY⟩, ?_, ⟨fun i j => ?_, fun i j => ?_⟩, ?_, ⟨fun i j => ?_, fun i j => ?_⟩, ?_⟩
  · intro w hw
    have hw' : w ≠ s.v := hw
    ext i j
    show compAt L w (θ (K i j, (1 : Matrix (Fin n) (Fin n) (AL L)) i j)) = _
    rw [hθw w hw', hc1]
  · show M K 1 i j ∈ ALint L
    rw [hM]
    exact add_mem (mul_mem heI (hKI i j)) (mul_mem (sub_mem (one_mem _) heI) (h1I i j))
  · obtain ⟨y, hy, hye⟩ := hκ.2 i j
    refine ⟨e * y, mul_mem heI hy, ?_⟩
    show M K 1 i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j = _
    rw [hM]
    linear_combination e * hye
  · intro w hw
    have hw' : w = s.v := by simpa using hw
    subst hw'
    ext i j
    show compAt L s.v (θ ((1 : Matrix (Fin n) (Fin n) (AL L)) i j, K i j)) = _
    rw [hθv, hc1]
  · show M 1 K i j ∈ ALint L
    rw [hM]
    exact add_mem (mul_mem heI (h1I i j)) (mul_mem (sub_mem (one_mem _) heI) (hKI i j))
  · obtain ⟨y, hy, hye⟩ := hκ.2 i j
    refine ⟨(1 - e) * y, mul_mem (sub_mem (one_mem _) heI) hy, ?_⟩
    show M 1 K i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j = _
    rw [hM]
    linear_combination (1 - e) * hye
  · apply Subtype.ext; apply Units.ext
    show K = M K 1 * M 1 K
    rw [M_mul, Matrix.mul_one, Matrix.one_mul, M_diag]

end GlobalTheory.IrrSplitSub

open GlobalTheory.IrrSplitSub in

theorem GlobalTheory.exists_irreducible_sub_trivOutside_split : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.FinTyp L n) (B : π.S → π.S → ℂ), (∀ x y z (c : ℂ), B x (y + c • z) = B x y + c * B x z) → (∀ x y, B x y = starRingEnd ℂ (B y x)) → (∀ x, x ≠ 0 → 0 < (B x x).re) → (∀ h (x y x' y' : π.S), (x' : GAf L n → ℂ) = NG.rt L n h x → (y' : GAf L n → ℂ) = NG.rt L n h y → B x' y' = B x y) → (∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ {f | f ∈ π.S ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f})) → ∀ s : SplitPlace L, ∃ W : Submodule ℂ (GAf L n → ℂ), W ≤ π.S ∧ W ≠ ⊥ ∧ (∀ x : GAf L n, TrivOutside {s.v} x → ∀ f ∈ W, NG.rt L n x f ∈ W) ∧ ∀ W' : Submodule ℂ (GAf L n → ℂ), W' ≤ W → (∀ x : GAf L n, TrivOutside {s.v} x → ∀ f ∈ W', NG.rt L n x f ∈ W') → W' = ⊥ ∨ W' = W := by
  intro L _ _ _ n π B hlin hherm hpos hinv hadm s
  classical
  have rt_apply : ∀ (h : GAf L n) (f : GAf L n → ℂ) g, NG.rt L n h f g = f (g * h) := fun _ _ _ => rfl
  have rt_mul : ∀ (a b : GAf L n) (f : GAf L n → ℂ), NG.rt L n (a * b) f = NG.rt L n a (NG.rt L n b f) := by
    intro a b f; funext g; rw [rt_apply, rt_apply, rt_apply, mul_assoc]
  have rt_one : ∀ f : GAf L n → ℂ, NG.rt L n 1 f = f := by
    intro f; funext g; rw [rt_apply, mul_one]
  have rt_inv : ∀ (x : GAf L n) (f : GAf L n → ℂ), NG.rt L n x (NG.rt L n x⁻¹ f) = f := by
    intro x f; rw [← rt_mul, mul_inv_cancel, rt_one]
  have B0r : ∀ x, B x 0 = 0 := fun x => by simpa using hlin x 0 0 1
  have Badd : ∀ x y z, B x (y + z) = B x y + B x z := fun x y z => by simpa using hlin x y z 1
  have Bsmul : ∀ x (c : ℂ) z, B x (c • z) = c * B x z := fun x c z => by simpa [B0r] using hlin x 0 z c
  have triv_one : TrivOutside {s.v} (1 : GAf L n) := fun w _ => by
    show (1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L w) = 1
    exact Matrix.map_one _ (map_zero _) (map_one _)

  let Fix : (GAf L n → Prop) → Submodule ℂ (GAf L n → ℂ) := fun P =>
    { carrier := {f | f ∈ π.S ∧ ∀ κ, P κ → NG.rt L n κ f = f}
      add_mem' := fun {a b} ha hb => ⟨π.S.add_mem ha.1 hb.1, fun κ hκ => by rw [map_add, ha.2 κ hκ, hb.2 κ hκ]⟩
      zero_mem' := ⟨π.S.zero_mem, fun κ _ => map_zero _⟩
      smul_mem' := fun c f hf => ⟨π.S.smul_mem c hf.1, fun κ hκ => by rw [map_smul, hf.2 κ hκ]⟩ }
  have finFix : ∀ M, 0 < M → FiniteDimensional ℂ (Fix (NG.Cong L n M)) := by
    intro M hM
    have h := hadm M hM
    have e : Submodule.span ℂ {f | f ∈ π.S ∧ ∀ κ, NG.Cong L n M κ → NG.rt L n κ f = f} =
        Fix (NG.Cong L n M) := Submodule.span_eq (Fix (NG.Cong L n M))
    rw [e] at h; exact h
  obtain ⟨f₀, hf₀S, hf₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne
  obtain ⟨N, hN, hf₀N⟩ := π.smooth f₀ hf₀S
  let VN := Fix (NG.Cong L n N)
  haveI : FiniteDimensional ℂ VN := finFix N hN
  let W₀ := Fix (fun y => NG.Cong L n N y ∧ TrivOutside {s.v}ᶜ y)
  let Hst : Submodule ℂ (GAf L n → ℂ) → Prop := fun U =>
    ∀ x : GAf L n, TrivOutside {s.v} x → ∀ f ∈ U, NG.rt L n x f ∈ U
  have W₀S : W₀ ≤ π.S := fun f hf => hf.1
  have W₀st : Hst W₀ := by
    intro x hx f hf
    refine ⟨π.stable x f hf.1, fun y hy => ?_⟩
    rw [← rt_mul, ← commute_of_trivOutside s hx hy.2, rt_mul, hf.2 y hy]
  let 𝒰 : Submodule ℂ (GAf L n → ℂ) → Prop := fun U => U ≤ W₀ ∧ Hst U ∧ U ⊓ VN ≠ ⊥
  have hex : ∃ d, ∃ U, 𝒰 U ∧ Module.finrank ℂ ↥(U ⊓ VN) = d := by
    refine ⟨_, W₀, ⟨le_rfl, W₀st, ?_⟩, rfl⟩
    rw [Submodule.ne_bot_iff]
    exact ⟨f₀, ⟨⟨hf₀S, fun y hy => hf₀N y hy.1⟩, ⟨hf₀S, hf₀N⟩⟩, hf₀ne⟩
  obtain ⟨U, hU, hUd⟩ := Nat.find_spec hex
  have hmin : ∀ U', 𝒰 U' → Nat.find hex ≤ Module.finrank ℂ ↥(U' ⊓ VN) :=
    fun U' hU' => Nat.find_min' hex ⟨U', hU', rfl⟩
  let X := U ⊓ VN
  haveI : FiniteDimensional ℂ X := Submodule.finiteDimensional_of_le inf_le_right
  let gen : Set (GAf L n → ℂ) := {g | ∃ x, TrivOutside {s.v} x ∧ ∃ f ∈ X, g = NG.rt L n x f}
  let Wsp := Submodule.span ℂ gen
  have hWU : Wsp ≤ U := Submodule.span_le.2 (by
    rintro _ ⟨x, hx, f, hf, rfl⟩; exact hU.2.1 x hx f hf.1)
  have hXW : X ≤ Wsp := fun f hf => Submodule.subset_span ⟨1, triv_one, f, hf, (rt_one f).symm⟩
  have Wst : Hst Wsp := by
    intro x hx f hf
    have : Wsp ≤ Wsp.comap (NG.rt L n x) := Submodule.span_le.2 (by
      rintro _ ⟨y, hy, g, hg, rfl⟩
      exact Submodule.subset_span ⟨x * y, GlobalTheory.SatInd.CosetFin.trivOutside_mul hx hy, g, hg, (rt_mul x y g).symm⟩)
    exact this hf
  have hWS : Wsp ≤ π.S := hWU.trans (hU.1.trans W₀S)
  refine ⟨Wsp, hWS, ?_, Wst, ?_⟩
  · intro h
    exact hU.2.2 (eq_bot_iff.2 (h ▸ hXW))
  intro W' hW'le hW'st
  by_cases hV : W' ⊓ VN = ⊥
  swap
  · right
    have h𝒰 : 𝒰 W' := ⟨hW'le.trans (hWU.trans hU.1), hW'st, hV⟩
    have hle : W' ⊓ VN ≤ X := inf_le_inf_right _ (hW'le.trans hWU)
    have heq : W' ⊓ VN = X := Submodule.eq_of_le_of_finrank_le hle (by rw [hUd]; exact hmin W' h𝒰)
    apply le_antisymm hW'le
    apply Submodule.span_le.2
    rintro _ ⟨x, hx, f, hf, rfl⟩
    have hf' : f ∈ W' ⊓ VN := heq ▸ hf
    exact hW'st x hx f hf'.1
  left
  have hW'S : W' ≤ π.S := hW'le.trans hWS

  let Bf : π.S →ₗ[ℂ] π.S →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun u v => B v u)
    (fun u₁ u₂ v => Badd v u₁ u₂) (fun c u v => Bsmul v c u)
    (fun u v₁ v₂ => by rw [hherm, Badd, map_add, ← hherm, ← hherm])
    (fun c u v => by rw [hherm, Bsmul, map_mul, ← hherm]; rfl)
  have hBf : ∀ u v, Bf u v = B v u := fun _ _ => rfl
  have hBfpos : ∀ v, v ≠ 0 → 0 < (Bf v v).re := fun v hv => by rw [hBf]; exact hpos v hv

  have key : ∀ w' (hw' : w' ∈ π.S), w' ∈ W' → ∀ f (hf : f ∈ π.S), f ∈ X → B ⟨w', hw'⟩ ⟨f, hf⟩ = 0 := by
    intro w' hw'S hw'W' f hfS hfX
    obtain ⟨N₁, hN₁, hw'N₁⟩ := π.smooth w' hw'S
    let F : Submodule ℂ π.S := (Fix (NG.Cong L n N₁)).comap π.S.subtype
    haveI := finFix N₁ hN₁
    haveI : FiniteDimensional ℂ F := by
      let φ : F →ₗ[ℂ] Fix (NG.Cong L n N₁) :=
        LinearMap.codRestrict (Fix (NG.Cong L n N₁)) (π.S.subtype ∘ₗ F.subtype) (fun c => c.2)
      refine Module.Finite.of_injective φ ?_
      intro a b h
      have h' := congrArg Subtype.val h
      apply Subtype.ext; apply Subtype.ext; exact h'
    let E : Submodule ℂ π.S := F ⊓ W'.comap π.S.subtype
    haveI : FiniteDimensional ℂ E := Submodule.finiteDimensional_of_le inf_le_left
    have stabE : ∀ k : GAf L n, k ∈ Umax L n → TrivOutside {s.v} k → ∀ v ∈ E,
        (⟨NG.rt L n k v, π.stable k v v.2⟩ : π.S) ∈ E := by
      intro k hkU hkT v hv
      refine ⟨⟨π.stable k v v.2, fun κ hκ => ?_⟩, hW'st k hkT v hv.2⟩
      have e : κ * k = k * (k⁻¹ * κ * k) := by group
      show NG.rt L n κ (NG.rt L n k (v : GAf L n → ℂ)) = NG.rt L n k (v : GAf L n → ℂ)
      have hfx : NG.rt L n (k⁻¹ * κ * k) (v : GAf L n → ℂ) = v := hv.1.2 _ (cong_conj hkU hκ)
      rw [← rt_mul, e, rt_mul, hfx]
    obtain ⟨u, huE, hu⟩ := GlobalTheory.SmoothRiesz.exists_mem_eq_on_of_finiteDimensional Bf hBfpos (Bf ⟨f, hfS⟩) E
    have hfixH : ∀ k, NG.Cong L n N k → TrivOutside {s.v} k → NG.rt L n k (u : GAf L n → ℂ) = u := by
      intro k hkC hkT
      let u' : π.S := ⟨NG.rt L n k u, π.stable k u u.2⟩
      have hu'E : u' ∈ E := stabE k hkC.1 hkT u huE
      have hsame : ∀ v ∈ E, Bf u' v = Bf u v := by
        intro v hv
        let v' : π.S := ⟨NG.rt L n k⁻¹ v, π.stable k⁻¹ v v.2⟩
        have hv'E : v' ∈ E := stabE k⁻¹ (Subgroup.inv_mem _ hkC.1)
          (GlobalTheory.SatInd.CosetFin.trivOutside_inv hkT) v hv
        have hkf : NG.rt L n k f = f := hfX.2.2 k hkC
        calc Bf u' v = B v u' := rfl
          _ = B v' u := hinv k v' u v u' (rt_inv k v).symm rfl
          _ = B v' ⟨f, hfS⟩ := (hu v' hv'E).symm
          _ = B v ⟨f, hfS⟩ := (hinv k v' ⟨f, hfS⟩ v ⟨f, hfS⟩ (rt_inv k v).symm hkf.symm).symm
          _ = Bf u v := hu v hv
      have hd : u' - u = 0 := by
        by_contra hne
        have h1 := hBfpos _ hne
        have h2 : Bf (u' - u) (u' - u) = 0 := by
          rw [show Bf (u' - u) = Bf u' - Bf u from map_sub Bf u' u, LinearMap.sub_apply,
            hsame _ (E.sub_mem hu'E huE), sub_self]
        rw [h2] at h1; simp at h1
      exact congrArg Subtype.val (sub_eq_zero.1 hd)
    have huW' : (u : GAf L n → ℂ) ∈ W' := huE.2
    have hfixK : ∀ κ, NG.Cong L n N κ → NG.rt L n κ (u : GAf L n → ℂ) = u := by
      intro κ hκ
      obtain ⟨x, y, hx, hxc, hy, hyc, rfl⟩ := cong_factor s N κ hκ
      have huW₀ : (u : GAf L n → ℂ) ∈ W₀ := (hW'le.trans (hWU.trans hU.1)) huW'
      rw [rt_mul, huW₀.2 y ⟨hyc, hy⟩, hfixH x hxc hx]
    have hu0 : u = 0 := by
      have hmem : (u : GAf L n → ℂ) ∈ W' ⊓ VN := ⟨huW', ⟨u.2, hfixK⟩⟩
      rw [hV, Submodule.mem_bot] at hmem
      exact Subtype.ext hmem
    have hw'E : (⟨w', hw'S⟩ : π.S) ∈ E := ⟨⟨hw'S, fun κ hκ => hw'N₁ κ hκ⟩, hw'W'⟩
    have := hu _ hw'E
    rw [hBf, hBf, hu0] at this
    rw [this]
    exact B0r _

  let Z : (w : GAf L n → ℂ) → w ∈ π.S → Submodule ℂ (GAf L n → ℂ) := fun w hw =>
    { carrier := {g | ∃ hg : g ∈ π.S, B ⟨w, hw⟩ ⟨g, hg⟩ = 0}
      add_mem' := fun {a b} ⟨ha, ha'⟩ ⟨hb, hb'⟩ => ⟨π.S.add_mem ha hb, by
        have := Badd ⟨w, hw⟩ ⟨a, ha⟩ ⟨b, hb⟩; rw [ha', hb', add_zero] at this; exact this⟩
      zero_mem' := ⟨π.S.zero_mem, B0r _⟩
      smul_mem' := fun c a ⟨ha, ha'⟩ => ⟨π.S.smul_mem c ha, by
        have := Bsmul ⟨w, hw⟩ c ⟨a, ha⟩; rw [ha', mul_zero] at this; exact this⟩ }
  rw [eq_bot_iff]
  intro w hw
  rw [Submodule.mem_bot]
  have hwS := hW'S hw
  have hWZ : Wsp ≤ Z w hwS := Submodule.span_le.2 (by
    rintro _ ⟨x, hx, f, hf, rfl⟩
    have hfS : f ∈ π.S := hf.2.1
    have hxw : NG.rt L n x⁻¹ w ∈ W' := hW'st x⁻¹ (GlobalTheory.SatInd.CosetFin.trivOutside_inv hx) w hw
    refine ⟨π.stable x f hfS, ?_⟩
    rw [hinv x ⟨NG.rt L n x⁻¹ w, hW'S hxw⟩ ⟨f, hfS⟩ ⟨w, hwS⟩ _ (rt_inv x w).symm rfl]
    exact key _ _ hxw f hfS hf)
  obtain ⟨_, hww⟩ := hWZ (hW'le hw)
  by_contra hne
  have := hpos ⟨w, hwS⟩ (fun h => hne (congrArg Subtype.val h))
  rw [hww] at this; simp at this
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_irreducible_subspace_trivialOutside_splitPlace : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.FinTyp L n) (B : π.S → π.S → ℂ), (∀ x y z (c : ℂ), B x (y + c • z) = B x y + c * B x z) → (∀ x y, B x y = starRingEnd ℂ (B y x)) → (∀ x, x ≠ 0 → 0 < (B x x).re) → (∀ h (x y x' y' : π.S), (x' : GAf L n → ℂ) = NG.rt L n h x → (y' : GAf L n → ℂ) = NG.rt L n h y → B x' y' = B x y) → (∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ {f | f ∈ π.S ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f})) → ∀ s : SplitPlace L, ∃ W : Submodule ℂ (GAf L n → ℂ), W ≤ π.S ∧ W ≠ ⊥ ∧ (∀ x : GAf L n, TrivOutside {s.v} x → ∀ f ∈ W, NG.rt L n x f ∈ W) ∧ ∀ W' : Submodule ℂ (GAf L n → ℂ), W' ≤ W → (∀ x : GAf L n, TrivOutside {s.v} x → ∀ f ∈ W', NG.rt L n x f ∈ W') → W' = ⊥ ∨ W' = W := by
  first | exact @GlobalTheory.exists_irreducible_sub_trivOutside_split | exact GlobalTheory.exists_irreducible_sub_trivOutside_split | (intros; apply GlobalTheory.exists_irreducible_sub_trivOutside_split <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitCongNbhd

theorem conjAL_entry (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (x : GAf L n) (i j : Fin n) :
    conjAL L (((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j)
      = (((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i := by
  have hx : ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      conjT (conjAL L) ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := x.2
  have h3 : (((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
    rw [← Units.val_mul]; simp
  have h2 : (((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      conjT (conjAL L) ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) := by
    calc _ = (((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
          (((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
            conjT (conjAL L) ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))) := by
            rw [hx, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h3, Matrix.one_mul]
  rw [h2]; simp [conjT, Matrix.transpose_apply, Matrix.map_apply]

theorem ringHom_one_apply {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (n : ℕ) (i j : Fin n) :
    f ((1 : Matrix (Fin n) (Fin n) R) i j) = (1 : Matrix (Fin n) (Fin n) S) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp

end GlobalTheory.SplitCongNbhd

open GlobalTheory.SplitCongNbhd in

theorem GlobalTheory.SplitCongNbhd.exists_nhds_one_cong (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (s : SplitPlace L) (N : ℕ) (hN : 0 < N) :
    ∃ U ∈ nhds (1 : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))),
      ∀ x : GAf L n, TrivOutside {s.v} x → s.loc n x ∈ U → NG.Cong L n N x := by
  set K := s.v.adicCompletion (maximalRealSubfield L)
  let U : Set (GL (Fin n) K) := {A | ∀ i j,
    Valued.v ((N : K)⁻¹ * ((A : Matrix (Fin n) (Fin n) K) i j - (1 : Matrix (Fin n) (Fin n) K) i j)) ≤ 1 ∧
    Valued.v ((N : K)⁻¹ * (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j -
      (1 : Matrix (Fin n) (Fin n) K) i j)) ≤ 1}
  refine ⟨U, ?_, ?_⟩
  · have hball : {t : K | Valued.v t ≤ 1} ∈ nhds (0 : K) :=
      (Valued.isOpen_integer K).mem_nhds (by simp [Valuation.mem_integer_iff])
    have key : ∀ f : GL (Fin n) K → K, Continuous f → f 1 = 0 →
        ∀ᶠ A in nhds (1 : GL (Fin n) K), Valued.v (f A) ≤ 1 := by
      intro f hf h1
      exact hf.continuousAt.preimage_mem_nhds (by rw [h1]; exact hball)
    have hc1 : ∀ i j, Continuous fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) i j := fun i j =>
      Units.continuous_val.matrix_elem i j
    have hc2 : ∀ i j, Continuous fun A : GL (Fin n) K =>
        ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j := fun i j =>
      Units.continuous_coe_inv.matrix_elem i j
    have hij : ∀ i j, ∀ᶠ (A : GL (Fin n) K) in nhds 1,
        Valued.v ((N : K)⁻¹ * ((A : Matrix (Fin n) (Fin n) K) i j - (1 : Matrix (Fin n) (Fin n) K) i j)) ≤ 1 ∧
        Valued.v ((N : K)⁻¹ * (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j -
          (1 : Matrix (Fin n) (Fin n) K) i j)) ≤ 1 := fun i j =>
      (key _ (continuous_const.mul ((hc1 i j).sub continuous_const)) (by simp)).and
        (key _ (continuous_const.mul ((hc2 i j).sub continuous_const)) (by simp))
    exact Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hij i j
  · intro x hx hU
    obtain ⟨e, he1, he2⟩ := GlobalTheory.SplitSep.exists_sep L s
    have hN' : (N : L) ≠ 0 := by exact_mod_cast hN.ne'
    set c : AL L := ((N : L)⁻¹) ⊗ₜ[maximalRealSubfield L] (1 : AFplus L) with hc
    have hNc : (N : AL L) * c = 1 := by
      rw [hc, Algebra.TensorProduct.natCast_def, Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hN',
        one_mul]; rfl
    have hconjc : conjAL L c = c := by
      rw [hc, GlobalTheory.SplitLift.conjAL_tmul, map_inv₀, map_natCast]
    have hprojc : s.proj c = (N : K)⁻¹ := by
      rw [hc, GlobalTheory.SplitLift.proj_tmul, map_inv₀, map_natCast]; simp
    set M : Matrix (Fin n) (Fin n) (AL L) := ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) with hM
    have hy : ∀ i j, c * (M i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j) ∈ ALint L := by
      intro i j
      refine GlobalTheory.mem_ALint_of_supported_at_split L s e he1 he2 _ ?_ ?_ ?_
      · intro w hw
        have h1 := congrFun (congrFun (hx w (by simpa using hw)) i) j
        rw [Matrix.map_apply] at h1
        rw [map_mul, map_sub, h1, ringHom_one_apply, sub_self, mul_zero]
      · rw [map_mul, map_sub, hprojc, ringHom_one_apply]
        exact (hU i j).1
      · have hinv : s.proj ((((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i) =
            ((((s.loc n x)⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) j i := by
          rw [← map_inv]; rfl
        have h1 : (1 : Matrix (Fin n) (Fin n) K) i j = (1 : Matrix (Fin n) (Fin n) K) j i := by
          simp [Matrix.one_apply, eq_comm]
        rw [map_mul, map_sub, hconjc, hM, conjAL_entry, ringHom_one_apply, map_mul, map_sub, hprojc, hinv,
          ringHom_one_apply, h1]
        exact (hU j i).2
    have hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := by
      intro i j; rw [Matrix.one_apply]; split_ifs
      · exact (ALint L).one_mem
      · exact (ALint L).zero_mem
    have hz : ∀ i j, M i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j =
        (N : AL L) * (c * (M i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j)) := by
      intro i j; rw [← mul_assoc, hNc, one_mul]
    refine ⟨?_, fun i j => ⟨_, hy i j, hz i j⟩⟩
    show ∀ i j, M i j ∈ ALint L
    intro i j
    have : M i j = (N : AL L) * (c * (M i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j)) +
        (1 : Matrix (Fin n) (Fin n) (AL L)) i j := by rw [← hz, sub_add_cancel]
    rw [this]
    exact (ALint L).add_mem ((ALint L).mul_mem (natCast_mem _ _) (hy i j)) (hone i j)
end

section
noncomputable section

namespace GlobalTheory.blockFieldPairProjections

open NumberField IsDedekindDomain ReciprocityTheory.Aut TensorProduct

section Completion

theorem exists_extension {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M]
    (u : HeightOneSpectrum (𝓞 K)) (t : HeightOneSpectrum (𝓞 M)) (f : K →+* t.adicCompletion M)
    (h1 : ∀ r : 𝓞 K, Valued.v (f r) ≤ 1) (h2 : ∀ r : 𝓞 K, Valued.v (f r) < 1 ↔ r ∈ u.asIdeal) :
    ∃ φ : u.adicCompletion K →+* t.adicCompletion M, Continuous φ ∧
      ∀ x, φ (algebraMap K (u.adicCompletion K) x) = f x := by
  have key : ∀ x : K, ‖algebraMap K (u.adicCompletion K) x‖ < 1 → ‖f x‖ < 1 := by
    intro x hx
    rw [Valued.toNormedField.norm_lt_one_iff] at hx ⊢
    rw [adic_valued_algebraMap] at hx
    obtain ⟨a, d, had⟩ := u.exists_primeCompl_mul_eq_of_integer x hx.le
    have hd : (d : 𝓞 K) ∉ u.asIdeal := d.2
    have ha : a ∈ u.asIdeal := by
      rw [← u.valuation_lt_one_iff_mem (K := K)]
      have := congrArg (u.valuation K) had
      rw [map_mul, u.valuation_eq_one_iff_notMem.2 hd, mul_one] at this
      exact this ▸ hx
    have hd1 : Valued.v (f (d : 𝓞 K)) = 1 := le_antisymm (h1 _) (not_lt.1 fun h => hd ((h2 _).1 h))
    have := congrArg (fun y => Valued.v (f y)) had
    simp only [map_mul] at this
    have e : Valued.v (f x) = Valued.v (f a) := by
      rw [← mul_one (Valued.v (f x)), ← hd1]; exact this
    rw [e]; exact (h2 a).2 ha
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot u.ne_bot
  have hpK : (p : K) ≠ 0 := fun h => hp0 (RingOfIntegers.coe_eq_zero_iff.1 h)
  have hfp : ‖f p‖ < 1 := Valued.toNormedField.norm_lt_one_iff.2 ((h2 p).2 hp)
  letI : PseudoMetricSpace K := PseudoMetricSpace.induced (algebraMap K (u.adicCompletion K)) inferInstance
  have ue : IsUniformInducing (algebraMap K (u.adicCompletion K)) := ⟨rfl⟩
  have dr := HeightOneSpectrum.denseRange_algebraMap K u
  have hf : UniformContinuous f := by
    rw [Metric.uniformContinuous_iff]
    intro ε hε
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hfp
    have hj : 0 < ‖algebraMap K (u.adicCompletion K) ((p : K) ^ k)‖ := by
      rw [norm_pos_iff, map_ne_zero]; exact pow_ne_zero _ hpK
    refine ⟨_, hj, fun {a b} hab => ?_⟩
    have hab' : ‖algebraMap K (u.adicCompletion K) (a - b)‖ < ‖algebraMap K (u.adicCompletion K) ((p : K) ^ k)‖ := by
      rw [map_sub, ← dist_eq_norm]; exact hab
    have h3 := key ((a - b) / (p : K) ^ k) (by rw [map_div₀, norm_div, div_lt_one hj]; exact hab')
    have hq : 0 < ‖f ((p : K) ^ k)‖ := by
      rw [norm_pos_iff, map_ne_zero]; exact pow_ne_zero _ hpK
    rw [map_div₀, norm_div, div_lt_one hq, map_sub, map_pow, norm_pow] at h3
    rw [dist_eq_norm]
    exact h3.trans hk
  exact ⟨IsDenseInducing.extendRingHom ue dr hf, (uniformContinuous_uniformly_extend ue dr hf).continuous,
    fun x => uniformly_extend_of_ind ue dr hf x⟩

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem exists_equiv (s : SplitPlace L) :
    ∃ e : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous e ∧ Continuous e.symm ∧
      ∀ x : L, e (s.i x) = algebraMap L (s.w.adicCompletion L) x := by
  obtain ⟨φ, hφc, hφ⟩ := exists_extension s.w s.v s.i.toRingHom (fun r => s.split_le_one r)
    (fun r => (s.split_mem_ideal r).symm)
  obtain ⟨ψ, hψc, hψ⟩ := exists_extension s.v s.w
    ((algebraMap L (s.w.adicCompletion L)).comp (algebraMap (maximalRealSubfield L) L))
    (fun r => by
      rw [RingHom.comp_apply, adic_valued_algebraMap, ← split_coe_algebraMap]
      exact s.w.valuation_le_one _)
    (fun r => by
      rw [RingHom.comp_apply, adic_valued_algebraMap, ← split_coe_algebraMap, ← s.split_alg_mem]
      exact s.w.valuation_lt_one_iff_mem _)
  have h1 : ∀ y, φ (ψ y) = y := by
    have := (HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield L) s.v).equalizer (hφc.comp hψc) continuous_id
      (by
        funext a
        simp only [Function.comp_apply, hψ, RingHom.comp_apply, hφ, id]
        exact s.i.commutes a)
    exact congrFun this
  have h2 : ∀ y, ψ (φ y) = y := fun y => φ.injective (h1 _)
  refine ⟨RingEquiv.ofRingHom ψ φ (RingHom.ext h2) (RingHom.ext h1), hψc, hφc, fun x => ?_⟩
  have := h2 (algebraMap L _ x)
  rw [hφ] at this
  exact this

end Completion

section Adeles

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => maximalRealSubfield L

theorem exists_imaginary (L : Type) [Field L] [NumberField L] [IsCMField L] :
    ∃ δ : 𝓞 L, (δ : L) ≠ 0 ∧ IsCMField.complexConj L (δ : L) = -(δ : L) := by
  have : ∃ y : 𝓞 L, IsCMField.complexConj L (y : L) ≠ y := by
    by_contra h
    push Not at h
    apply IsCMField.complexConj_ne_one L
    ext x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) x
    rw [map_div₀]
    exact congrArg₂ (· / ·) (h a) (h b)
  obtain ⟨y, hy⟩ := this
  refine ⟨y - IsCMField.ringOfIntegersComplexConj L y, ?_, ?_⟩
  · have : ((y - IsCMField.ringOfIntegersComplexConj L y : 𝓞 L) : L) = y - IsCMField.complexConj L y := by
      rw [← IsCMField.coe_ringOfIntegersComplexConj]; rfl
    rw [this]
    exact sub_ne_zero.2 hy.symm
  · have : ((y - IsCMField.ringOfIntegersComplexConj L y : 𝓞 L) : L) = y - IsCMField.complexConj L y := by
      rw [← IsCMField.coe_ringOfIntegersComplexConj]; rfl
    rw [this, map_sub, IsCMField.complexConj_apply_apply, neg_sub]

theorem exists_basis {δ : L} (h0 : δ ≠ 0) (hδ : IsCMField.complexConj L δ = -δ) :
    ∃ b : Module.Basis (Fin 2) L⁺ L, b 0 = 1 ∧ b 1 = δ := by
  have hli : LinearIndependent L⁺ ![(1 : L), δ] := by
    rw [LinearIndependent.pair_iff]
    intro a t h
    rw [Algebra.smul_def, Algebra.smul_def] at h
    have h' := congrArg (IsCMField.complexConj L) h
    rw [map_add, map_mul, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, map_one, hδ, map_zero] at h'
    have h1 : algebraMap L⁺ L a = 0 := by linear_combination (h + h') / 2
    have h2 : algebraMap L⁺ L t * δ = 0 := by linear_combination (h - h') / 2
    exact ⟨(map_eq_zero _).1 h1, (map_eq_zero _).1 ((mul_eq_zero.1 h2).resolve_right h0)⟩
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli ?_, ?_, ?_⟩
  · rw [Algebra.IsQuadraticExtension.finrank_eq_two L⁺ L]; simp
  · simp
  · simp

theorem exists_coords {F V A : Type} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup A] [Module F A]
    (b : Module.Basis (Fin 2) F V) (z : V ⊗[F] A) : ∃ x y : A, z = b 0 ⊗ₜ x + b 1 ⊗ₜ y := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul v a =>
    refine ⟨b.repr v 0 • a, b.repr v 1 • a, ?_⟩
    conv_lhs => rw [← b.sum_repr v]
    rw [Fin.sum_univ_two, add_tmul, smul_tmul, smul_tmul]
  | add z z' h h' =>
    obtain ⟨x, y, rfl⟩ := h
    obtain ⟨x', y', rfl⟩ := h'
    exact ⟨x + x', y + y', by rw [tmul_add, tmul_add]; abel⟩

theorem coords_eq_zero {F V A : Type} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup A] [Module F A]
    (b : Module.Basis (Fin 2) F V) {x y : A} (h : b 0 ⊗ₜ[F] x + b 1 ⊗ₜ[F] y = 0) : x = 0 ∧ y = 0 := by
  have h0 := congrArg ((TensorProduct.lid F A).toLinearMap ∘ₗ LinearMap.rTensor A (b.coord 0)) h
  have h1 := congrArg ((TensorProduct.lid F A).toLinearMap ∘ₗ LinearMap.rTensor A (b.coord 1)) h
  exact ⟨by simpa using h0, by simpa using h1⟩

theorem proj_tmul (s : SplitPlace L) (x : L) (a : AFplus L) : s.proj (x ⊗ₜ a) = s.i x * a s.v := rfl

theorem conj_tmul (x : L) (a : AFplus L) : conjAL L (x ⊗ₜ a) = IsCMField.complexConj L x ⊗ₜ a := rfl

theorem comp_tmul (u : HeightOneSpectrum (𝓞 L⁺)) (x : L) (a : AFplus L) : compAt L u (x ⊗ₜ a) = x ⊗ₜ a u := rfl

theorem adele_ext (s : SplitPlace L) {z z' : AL L} (h1 : s.proj z = s.proj z')
    (h2 : s.proj (conjAL L z) = s.proj (conjAL L z')) (h3 : ∀ u, u ≠ s.v → compAt L u z = compAt L u z') : z = z' := by
  obtain ⟨δ, h0, hδ⟩ := exists_imaginary L
  obtain ⟨b, hb0, hb1⟩ := exists_basis h0 hδ
  rw [← sub_eq_zero, ← map_sub] at h1
  rw [← sub_eq_zero, ← map_sub, ← map_sub] at h2
  have h3' : ∀ u, u ≠ s.v → compAt L u (z - z') = 0 := fun u hu => by rw [map_sub, h3 u hu, sub_self]
  rw [← sub_eq_zero]
  obtain ⟨x, y, hz⟩ := exists_coords b (z - z')
  rw [hz] at h1 h2 h3' ⊢
  have hd : s.i δ ≠ 0 := (map_ne_zero s.i).2 h0
  haveI : CharZero (s.v.adicCompletion L⁺) := charZero_of_injective_algebraMap (algebraMap L⁺ _).injective
  rw [map_add, proj_tmul, proj_tmul, hb0, hb1, map_one] at h1
  rw [map_add, map_add, conj_tmul, conj_tmul, proj_tmul, proj_tmul, hb0, hb1, map_one, map_one, hδ, map_neg] at h2
  have key : ∀ u, x u = 0 ∧ y u = 0 := by
    intro u
    by_cases hu : u = s.v
    · subst hu
      have hy : s.i δ * y s.v = 0 := by linear_combination (h1 - h2) / 2
      exact ⟨by linear_combination (h1 + h2) / 2, (mul_eq_zero.1 hy).resolve_left hd⟩
    · have := h3' u hu
      rw [map_add, comp_tmul, comp_tmul] at this
      exact coords_eq_zero b this
  have hx : x = 0 := FiniteAdeleRing.ext _ fun u => (key u).1
  have hy : y = 0 := FiniteAdeleRing.ext _ fun u => (key u).2
  rw [hx, hy]; simp

open Classical in

def single (v : HeightOneSpectrum (𝓞 L⁺)) (a : v.adicCompletion L⁺) : AFplus L :=
  ⟨Pi.single (M := fun u : HeightOneSpectrum (𝓞 L⁺) => u.adicCompletion L⁺) v a, by
    filter_upwards [(Set.finite_singleton v).compl_mem_cofinite] with u hu
    rw [Pi.single_eq_of_ne hu]
    exact zero_mem _⟩

theorem single_self (v : HeightOneSpectrum (𝓞 L⁺)) (a : v.adicCompletion L⁺) : single v a v = a := by
  classical
  exact Pi.single_eq_same (M := fun u : HeightOneSpectrum (𝓞 L⁺) => u.adicCompletion L⁺) v a

theorem single_ne {v u : HeightOneSpectrum (𝓞 L⁺)} (h : u ≠ v) (a : v.adicCompletion L⁺) : single v a u = 0 := by
  classical
  exact Pi.single_eq_of_ne (M := fun u : HeightOneSpectrum (𝓞 L⁺) => u.adicCompletion L⁺) h a

theorem single_mul (v : HeightOneSpectrum (𝓞 L⁺)) (N : ℕ) (a : v.adicCompletion L⁺) :
    single v (N * a) = N • single v a := by
  refine FiniteAdeleRing.ext _ fun u => ?_
  have : (N • single v a) u = N • single v a u := map_nsmul (evalAt L u) N _
  rw [this]
  by_cases hu : u = v
  · subst hu; rw [single_self, single_self, nsmul_eq_mul]
  · rw [single_ne hu, single_ne hu, smul_zero]

def pair (s : SplitPlace L) (δ : L) (a b : s.v.adicCompletion L⁺) : AL L :=
  1 ⊗ₜ single s.v ((a + b) / 2) + δ ⊗ₜ single s.v ((a - b) / (2 * s.i δ))

theorem proj_pair (s : SplitPlace L) {δ : L} (h0 : δ ≠ 0) (a b : s.v.adicCompletion L⁺) : s.proj (pair s δ a b) = a := by
  have hd : s.i δ ≠ 0 := (map_ne_zero s.i).2 h0
  haveI : CharZero (s.v.adicCompletion L⁺) := charZero_of_injective_algebraMap (algebraMap L⁺ _).injective
  rw [pair, map_add, proj_tmul, proj_tmul, single_self, single_self, map_one]
  field_simp
  ring

theorem proj_conj_pair (s : SplitPlace L) {δ : L} (h0 : δ ≠ 0) (hδ : IsCMField.complexConj L δ = -δ)
    (a b : s.v.adicCompletion L⁺) : s.proj (conjAL L (pair s δ a b)) = b := by
  have hd : s.i δ ≠ 0 := (map_ne_zero s.i).2 h0
  haveI : CharZero (s.v.adicCompletion L⁺) := charZero_of_injective_algebraMap (algebraMap L⁺ _).injective
  rw [pair, map_add, map_add, conj_tmul, conj_tmul, proj_tmul, proj_tmul, single_self, single_self, map_one, map_one,
    hδ, map_neg]
  field_simp
  ring

theorem comp_pair (s : SplitPlace L) (δ : L) (a b : s.v.adicCompletion L⁺) {u : HeightOneSpectrum (𝓞 L⁺)} (h : u ≠ s.v) :
    compAt L u (pair s δ a b) = 0 := by
  rw [pair, map_add, comp_tmul, comp_tmul, single_ne h, single_ne h, tmul_zero, tmul_zero, add_zero]

theorem comp_conj_pair (s : SplitPlace L) (δ : L) (a b : s.v.adicCompletion L⁺) {u : HeightOneSpectrum (𝓞 L⁺)}
    (h : u ≠ s.v) : compAt L u (conjAL L (pair s δ a b)) = 0 := by
  rw [pair, map_add, map_add, conj_tmul, conj_tmul, comp_tmul, comp_tmul, single_ne h, single_ne h, tmul_zero, tmul_zero,
    add_zero]

theorem one_tmul_single_mem {v : HeightOneSpectrum (𝓞 L⁺)} {a : v.adicCompletion L⁺}
    (ha : a ∈ v.adicCompletionIntegers L⁺) : (1 : L) ⊗ₜ[L⁺] single v a ∈ ALint L := by
  refine Subring.subset_closure (Or.inr ⟨_, fun u => ?_, rfl⟩)
  by_cases hu : u = v
  · subst hu; rwa [single_self]
  · rw [single_ne hu]; exact zero_mem _

theorem pair_div (s : SplitPlace L) (δ : 𝓞 L) {N : ℕ} (hN : 0 < N) {a b : s.v.adicCompletion L⁺}
    (h1 : (a + b) / 2 / N ∈ s.v.adicCompletionIntegers L⁺)
    (h2 : (a - b) / (2 * s.i δ) / N ∈ s.v.adicCompletionIntegers L⁺) :
    ∃ y ∈ ALint L, pair s δ a b = (N : AL L) * y := by
  haveI : CharZero (s.v.adicCompletion L⁺) := charZero_of_injective_algebraMap (algebraMap L⁺ _).injective
  have hN' : (N : s.v.adicCompletion L⁺) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hδ : (δ : L) ⊗ₜ[L⁺] (1 : AFplus L) ∈ ALint L := Subring.subset_closure (Or.inl ⟨δ, rfl⟩)
  refine ⟨_, add_mem (one_tmul_single_mem h1) (mul_mem hδ (one_tmul_single_mem h2)), ?_⟩
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← nsmul_eq_mul, smul_add, ← tmul_smul, ← tmul_smul,
    ← single_mul, ← single_mul, mul_div_cancel₀ _ hN', mul_div_cancel₀ _ hN', pair]

end Adeles

section Group

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

local notation3 "L⁺" => maximalRealSubfield L

open Matrix

theorem matrix_ext (s : SplitPlace L) {X Y : Matrix (Fin n) (Fin n) (AL L)} (h1 : X.map s.proj = Y.map s.proj)
    (h2 : X.map (s.proj.comp (conjAL L)) = Y.map (s.proj.comp (conjAL L)))
    (h3 : ∀ u, u ≠ s.v → X.map (compAt L u) = Y.map (compAt L u)) : X = Y := by
  ext i j
  exact adele_ext s (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)
    fun u hu => congrFun (congrFun (h3 u hu) i) j

theorem map_conjT {R T : Type} [CommRing R] [CommRing T] (σ : R →+* R) (φ : R →+* T) (X : Matrix (Fin n) (Fin n) R) :
    (conjT σ X).map φ = (X.map (φ.comp σ))ᵀ := rfl

def liftMat (s : SplitPlace L) (δ : L) (g : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (AL L) :=
  1 + Matrix.of fun i j => pair s δ ((g.val - 1) i j) (((g⁻¹).val - 1) j i)

theorem map_one_add {R T : Type} [CommRing R] [CommRing T] (φ : R →+* T) (X : Matrix (Fin n) (Fin n) R) :
    (1 + X).map φ = 1 + X.map φ := by
  rw [← RingHom.mapMatrix_apply, map_add, map_one, RingHom.mapMatrix_apply]

theorem liftMat_proj (s : SplitPlace L) {δ : L} (h0 : δ ≠ 0) (g : GL (Fin n) (s.v.adicCompletion L⁺)) :
    (liftMat s δ g).map s.proj = g.val := by
  rw [liftMat, map_one_add]
  ext i j
  simp [proj_pair s h0]

theorem liftMat_proj_conj (s : SplitPlace L) {δ : L} (h0 : δ ≠ 0) (hδ : IsCMField.complexConj L δ = -δ)
    (g : GL (Fin n) (s.v.adicCompletion L⁺)) :
    (liftMat s δ g).map (s.proj.comp (conjAL L)) = (g⁻¹).valᵀ := by
  rw [liftMat, map_one_add]
  ext i j
  simp [proj_conj_pair s h0 hδ, Matrix.one_apply, eq_comm]

theorem liftMat_comp (s : SplitPlace L) (δ : L) (g : GL (Fin n) (s.v.adicCompletion L⁺))
    {u : HeightOneSpectrum (𝓞 L⁺)} (h : u ≠ s.v) : (liftMat s δ g).map (compAt L u) = 1 := by
  rw [liftMat, map_one_add]
  ext i j
  simp [comp_pair s δ _ _ h]

theorem liftMat_comp_conj (s : SplitPlace L) (δ : L) (g : GL (Fin n) (s.v.adicCompletion L⁺))
    {u : HeightOneSpectrum (𝓞 L⁺)} (h : u ≠ s.v) : (liftMat s δ g).map ((compAt L u).comp (conjAL L)) = 1 := by
  rw [liftMat, map_one_add]
  ext i j
  simp [comp_conj_pair s δ _ _ h]

theorem comp_conj_conj {T : Type} [CommRing T] (φ : AL L →+* T) : (φ.comp (conjAL L)).comp (conjAL L) = φ :=
  RingHom.ext fun x => congrArg φ (conjAL_conjAL L x)

theorem liftMat_unitary (s : SplitPlace L) {δ : L} (h0 : δ ≠ 0) (hδ : IsCMField.complexConj L δ = -δ)
    (g : GL (Fin n) (s.v.adicCompletion L⁺)) : liftMat s δ g * conjT (conjAL L) (liftMat s δ g) = 1 := by
  refine matrix_ext s ?_ ?_ fun u hu => ?_
  · rw [Matrix.map_mul, map_conjT, liftMat_proj s h0, liftMat_proj_conj s h0 hδ, transpose_transpose, Units.mul_inv,
      Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [Matrix.map_mul, map_conjT, comp_conj_conj, liftMat_proj s h0, liftMat_proj_conj s h0 hδ, ← transpose_mul,
      Units.mul_inv, transpose_one, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [Matrix.map_mul, map_conjT, liftMat_comp s δ g hu, liftMat_comp_conj s δ g hu, transpose_one, mul_one,
      Matrix.map_one _ (map_zero _) (map_one _)]

def liftG (s : SplitPlace L) {δ : L} (h0 : δ ≠ 0) (hδ : IsCMField.complexConj L δ = -δ)
    (g : GL (Fin n) (s.v.adicCompletion L⁺)) : GA L n :=
  ⟨⟨liftMat s δ g, conjT (conjAL L) (liftMat s δ g), liftMat_unitary s h0 hδ g,
    mul_eq_one_comm.1 (liftMat_unitary s h0 hδ g)⟩, liftMat_unitary s h0 hδ g⟩

theorem loc_liftG (s : SplitPlace L) {δ : L} (h0 : δ ≠ 0) (hδ : IsCMField.complexConj L δ = -δ)
    (g : GL (Fin n) (s.v.adicCompletion L⁺)) : s.loc n (liftG s h0 hδ g) = g :=
  Units.ext (liftMat_proj s h0 g)

theorem triv_liftG (s : SplitPlace L) {δ : L} (h0 : δ ≠ 0) (hδ : IsCMField.complexConj L δ = -δ)
    (g : GL (Fin n) (s.v.adicCompletion L⁺)) : TrivOutside {s.v} (liftG s h0 hδ g) :=
  fun _ hu => liftMat_comp s δ g hu

theorem triv_mul {T : Set (HeightOneSpectrum (𝓞 L⁺))} {x y : GA L n} (hx : TrivOutside T x) (hy : TrivOutside T y) :
    TrivOutside T (x * y) := fun u hu => by
  rw [Subgroup.coe_mul, Units.val_mul, Matrix.map_mul, hx u hu, hy u hu, mul_one]

theorem eq_of_loc_eq (s : SplitPlace L) {x y : GA L n} (hx : TrivOutside {s.v} x) (hy : TrivOutside {s.v} y)
    (h : s.loc n x = s.loc n y) : x = y := by
  have h1 : x.1.val.map s.proj = y.1.val.map s.proj := congrArg Units.val h
  have inv : ∀ z : GA L n, z.1.val.map s.proj * (z.1.val.map (s.proj.comp (conjAL L)))ᵀ = 1 := fun z => by
    have hz : z.1.val * conjT (conjAL L) z.1.val = 1 := z.2
    rw [← map_conjT, ← Matrix.map_mul, hz, Matrix.map_one _ (map_zero _) (map_one _)]
  refine Subtype.ext (Units.ext (matrix_ext s h1 ?_ fun u hu => (hx u hu).trans (hy u hu).symm))
  have a := inv x
  rw [h1] at a
  exact transpose_injective (Matrix.right_inv_eq_right_inv a (inv y))

def liftHom (s : SplitPlace L) {δ : L} (h0 : δ ≠ 0) (hδ : IsCMField.complexConj L δ = -δ) :
    GL (Fin n) (s.v.adicCompletion L⁺) →* GA L n :=
  MonoidHom.mk' (liftG s h0 hδ) fun a b =>
    eq_of_loc_eq s (triv_liftG s h0 hδ _) (triv_mul (triv_liftG s h0 hδ _) (triv_liftG s h0 hδ _))
      (by rw [map_mul, loc_liftG, loc_liftG, loc_liftG])

theorem eventually_cong (s : SplitPlace L) {δ : 𝓞 L} (h0 : (δ : L) ≠ 0) (hδ : IsCMField.complexConj L δ = -δ)
    {N : ℕ} (hN : 0 < N) :
    ∀ᶠ g in nhds (1 : GL (Fin n) (s.v.adicCompletion L⁺)), Formalism.L2.NG.Cong L n N (liftG s h0 hδ g) := by
  have ho : IsOpen (s.v.adicCompletionIntegers L⁺ : Set (s.v.adicCompletion L⁺)) := Valued.isOpen_valuationSubring _
  have ca : ∀ i j, Continuous fun g : GL (Fin n) (s.v.adicCompletion L⁺) => (g.val - 1) i j := fun i j =>
    (Units.continuous_val.sub continuous_const).matrix_elem i j
  have cb : ∀ i j, Continuous fun g : GL (Fin n) (s.v.adicCompletion L⁺) => ((g⁻¹).val - 1) i j := fun i j =>
    (Units.continuous_coe_inv.sub continuous_const).matrix_elem i j
  have key : ∀ᶠ g in nhds (1 : GL (Fin n) (s.v.adicCompletion L⁺)), ∀ i j, ∃ y ∈ ALint L,
      pair s δ ((g.val - 1) i j) (((g⁻¹).val - 1) j i) = (N : AL L) * y := by
    simp only [Filter.eventually_all]
    intro i j
    have e1 := ((((ca i j).add (cb j i)).div_const 2).div_const (N : s.v.adicCompletion L⁺)).continuousAt.eventually_mem
      (x := 1) (ho.mem_nhds (by simp))
    have e2 := ((((ca i j).sub (cb j i)).div_const (2 * s.i δ)).div_const
      (N : s.v.adicCompletion L⁺)).continuousAt.eventually_mem (x := 1) (ho.mem_nhds (by simp))
    filter_upwards [e1, e2] with g h1 h2
    exact pair_div s δ hN h1 h2
  filter_upwards [key] with g hg
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · obtain ⟨y, hy, e⟩ := hg i j
    show liftMat s δ g i j ∈ ALint L
    rw [liftMat, Matrix.add_apply, Matrix.of_apply, e]
    refine add_mem ?_ (mul_mem (natCast_mem _ _) hy)
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · obtain ⟨y, hy, e⟩ := hg i j
    refine ⟨y, hy, ?_⟩
    show liftMat s δ g i j - _ = _
    rw [liftMat, Matrix.add_apply, Matrix.of_apply, e, add_sub_cancel_left]

end Group

open Formalism.AUTREP Formalism.L2.NG in

theorem exists_local_component {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (π : FinTyp L n) (s : SplitPlace L)
    (W : Submodule ℂ (GAf L n → ℂ)) (hW : W ≤ π.S) (h0 : W ≠ ⊥)
    (hst : ∀ x : GAf L n, TrivOutside {s.v} x → ∀ f ∈ W, rt L n x f ∈ W)
    (hirr : ∀ W' ≤ W, (∀ x : GAf L n, TrivOutside {s.v} x → ∀ f ∈ W', rt L n x f ∈ W') → W' = ⊥ ∨ W' = W) :
    ∃ τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)), GlobalTheory.HeightCounting.IsLocS π.S s τ := by
  obtain ⟨e, he, he', hei⟩ := exists_equiv s
  obtain ⟨δ, hδ0, hδ⟩ := exists_imaginary L
  let b : GL (Fin n) (s.w.adicCompletion L) →* GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) :=
    Matrix.GeneralLinearGroup.map e.symm.toRingHom
  have hb : Continuous b := by
    refine Units.continuous_iff.2 ⟨Units.continuous_val.matrix_map he', ?_⟩
    simp only [← map_inv]
    exact Units.continuous_coe_inv.matrix_map he'
  have hbe : ∀ g, b (Matrix.GeneralLinearGroup.map e.toRingHom g) = g := fun g =>
    Units.ext (Matrix.ext fun i j => e.symm_apply_apply _)
  let ι : GL (Fin n) (s.w.adicCompletion L) →* GAf L n := (liftHom s hδ0 hδ).comp b
  have hι : ∀ g, TrivOutside {s.v} (ι g) := fun g => triv_liftG s hδ0 hδ _
  have hιx : ∀ x : GAf L n, TrivOutside {s.v} x → ι (Matrix.GeneralLinearGroup.map e.toRingHom (s.loc n x)) = x := by
    intro x hx
    refine eq_of_loc_eq s (hι _) hx ?_
    exact (loc_liftG s hδ0 hδ _).trans (hbe _)
  let ρ : Representation ℂ (GL (Fin n) (s.w.adicCompletion L)) W :=
    { toFun := fun g => (rt L n (ι g)).restrict (hst _ (hι g))
      map_one' := by
        ext f x
        show f.1 (x * ι 1) = f.1 x
        rw [map_one, mul_one]
      map_mul' := fun g h => by
        ext f x
        show f.1 (x * ι (g * h)) = f.1 (x * ι g * ι h)
        rw [map_mul, mul_assoc] }
  have hρ : ∀ g (f : W), (ρ g f : GAf L n → ℂ) = rt L n (ι g) f := fun _ _ => rfl
  have hsm : GlobalTheory.PRep.IsSmooth ρ := by
    intro f
    obtain ⟨N, hN, hf⟩ := π.smooth f (hW f.2)
    let K : Subgroup (GL (Fin n) (s.w.adicCompletion L)) :=
      { carrier := {g | ρ g f = f}
        one_mem' := by simp
        mul_mem' := fun {g h} hg hh => by
          have hg' : ρ g f = f := hg
          have hh' : ρ h f = f := hh
          show ρ (g * h) f = f
          rw [map_mul, Module.End.mul_apply, hh', hg']
        inv_mem' := fun {g} hg => by
          have hg' : ρ g f = f := hg
          show ρ g⁻¹ f = f
          conv_lhs => rw [← hg', ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
          rfl }
    refine K.isOpen_of_mem_nhds (g := 1) ?_
    have h1 := eventually_cong (n := n) s hδ0 hδ hN
    rw [← map_one b] at h1
    filter_upwards [hb.continuousAt.eventually h1] with g hg
    exact Subtype.ext (hf _ hg)
  have hir : ρ.IsIrreducible := by
    have hnt : Nontrivial (Subrepresentation ρ) := ⟨⊥, ⊤, fun h => h0 <| (Submodule.eq_bot_iff _).2 fun f hf => by
      have : (⟨f, hf⟩ : W) ∈ (⊥ : Subrepresentation ρ).toSubmodule := by rw [h]; trivial
      exact congrArg Subtype.val (show (⟨f, hf⟩ : W) = 0 from this)⟩
    refine ⟨fun R => ?_⟩
    rcases hirr (R.toSubmodule.map W.subtype) (Submodule.map_subtype_le _ _) (by
      rintro x hx _ ⟨f, hf, rfl⟩
      exact ⟨_, R.apply_mem_toSubmodule (Matrix.GeneralLinearGroup.map e.toRingHom (s.loc n x)) hf, by
        rw [Submodule.subtype_apply, hρ, hιx x hx]; rfl⟩) with h | h
    · left
      refine le_antisymm (fun f hf => ?_) bot_le
      have : (f : GAf L n → ℂ) ∈ R.toSubmodule.map W.subtype := ⟨f, hf, rfl⟩
      rw [h] at this
      exact Subtype.ext this
    · right
      refine le_antisymm le_top fun f _ => ?_
      have : (f : GAf L n → ℂ) ∈ R.toSubmodule.map W.subtype := by rw [h]; exact f.2
      obtain ⟨f', hf', e'⟩ := this
      obtain rfl : f' = f := Subtype.ext e'
      exact hf'
  refine ⟨⟨W, ρ, hsm, hir⟩, e, W.subtype, he, hei, W.injective_subtype, fun a => hW a.2, fun x hx a => ?_⟩
  exact (hρ _ a).trans (by rw [hιx x hx]; rfl)

end GlobalTheory.blockFieldPairProjections
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowLocal

open Formalism.IndefR.principalLevelFrame in

theorem finTyp_fixed_finiteDimensional : ∀ (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (j : ℕ) (X : RowMod D rep j) (σ : D.what₂.FT), Formalism.IndefR.principalLevelFrame.isotIn (D := D) X.ρ X.C (rep σ) ≠ ⊥ → ∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ {f | f ∈ (rep σ).S ∧ ∀ κ, NG.Cong D.host.E D.R.r N κ → NG.rt D.host.E D.R.r κ f = f}) := by
  intro D rep j X σ hne N hN
  obtain ⟨Φ, ⟨hΦe, hΦC⟩, hΦne⟩ : ∃ Φ : (rep σ).S →ₗ[ℂ] X.A,
      (IsEqvA X.ρ (rep σ) Φ ∧ LinearMap.range Φ ≤ X.C) ∧ LinearMap.range Φ ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    apply hne
    unfold Formalism.IndefR.principalLevelFrame.isotIn
    exact iSup_eq_bot.2 fun Φ => iSup_eq_bot.2 fun hΦ => hcon Φ hΦ
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot]
    let S' : Submodule ℂ (GAf D.host.E D.R.r → ℂ) := (LinearMap.ker Φ).map (rep σ).S.subtype
    have hS'le : S' ≤ (rep σ).S := by
      rintro f ⟨k, _, rfl⟩
      exact k.2
    have hS'st : ∀ h, ∀ f ∈ S', NG.rt D.host.E D.R.r h f ∈ S' := by
      rintro h f ⟨k, hk, rfl⟩
      refine ⟨⟨NG.rt D.host.E D.R.r h k, (rep σ).stable h k k.2⟩, ?_, rfl⟩
      show Φ _ = 0
      rw [hΦe h k, LinearMap.mem_ker.1 hk, map_zero]
    rcases (rep σ).irr S' hS'le hS'st with h0 | hall
    · rw [eq_bot_iff]
      intro k hk
      have : (k : GAf D.host.E D.R.r → ℂ) ∈ S' := ⟨k, hk, rfl⟩
      rw [h0, Submodule.mem_bot] at this
      exact (Submodule.mem_bot ℂ).2 (Subtype.ext this)
    · exfalso
      apply hΦne
      rw [eq_bot_iff]
      rintro a ⟨y, rfl⟩
      have : (y : GAf D.host.E D.R.r → ℂ) ∈ S' := by rw [hall]; exact y.2
      obtain ⟨k, hk, hky⟩ := this
      rw [show y = k from Subtype.ext hky.symm]
      exact (Submodule.mem_bot ℂ).2 (LinearMap.mem_ker.1 hk)
  set F := Submodule.span ℂ {f | f ∈ (rep σ).S ∧ ∀ κ, NG.Cong D.host.E D.R.r N κ → NG.rt D.host.E D.R.r κ f = f} with hF
  set T := Submodule.span ℂ {x | x ∈ X.C ∧ ∀ κ, NG.Cong D.host.E D.R.r N κ → X.ρ κ x = x} with hT
  have := X.adm N hN
  have hFS : F ≤ (rep σ).S := Submodule.span_le.2 fun f hf => hf.1
  have hFT : ∀ f (hf : f ∈ F), Φ ⟨f, hFS hf⟩ ∈ T := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      refine Submodule.subset_span ⟨hΦC ⟨_, rfl⟩, fun κ hκ => ?_⟩
      rw [← hΦe κ]
      congr 1
      exact Subtype.ext (hx.2 κ hκ)
    | zero =>
      have : (⟨0, hFS F.zero_mem⟩ : (rep σ).S) = 0 := rfl
      rw [this, map_zero]
      exact T.zero_mem
    | add x y hx hy ihx ihy =>
      have : (⟨x + y, hFS (F.add_mem hx hy)⟩ : (rep σ).S) = ⟨x, hFS hx⟩ + ⟨y, hFS hy⟩ := rfl
      rw [this, map_add]
      exact T.add_mem ihx ihy
    | smul a x hx ih =>
      have : (⟨a • x, hFS (F.smul_mem a hx)⟩ : (rep σ).S) = a • ⟨x, hFS hx⟩ := rfl
      rw [this, map_smul]
      exact T.smul_mem a ih
  let g : F →ₗ[ℂ] T := LinearMap.codRestrict T (Φ ∘ₗ Submodule.inclusion hFS) (fun f => hFT f f.2)
  have hg : Function.Injective g := by
    intro a b hab
    have h1 : Φ (Submodule.inclusion hFS a) = Φ (Submodule.inclusion hFS b) := congrArg Subtype.val hab
    exact Submodule.inclusion_injective hFS (hinj h1)
  exact Module.Finite.of_injective g hg

end GlobalTheory.RowLocal

namespace GlobalTheory.RowLocal

section Asm
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem trivOutside_mul {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x y : GAf L n}
    (hx : TrivOutside T x) (hy : TrivOutside T y) : TrivOutside T (x * y) := by
  intro v hv
  have h1 := hx v hv
  have h2 := hy v hv
  show ((x.1 * y.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = 1
  rw [Units.val_mul, Matrix.map_mul, h1, h2, mul_one]

theorem isLocS_of_irr (π : NG.FinTyp L n) (s : SplitPlace L) (W : Submodule ℂ (GAf L n → ℂ)) (hWS : W ≤ π.S)
    (hW0 : W ≠ ⊥) (hst : ∀ x : GAf L n, TrivOutside {s.v} x → ∀ f ∈ W, NG.rt L n x f ∈ W)
    (hirr : ∀ W' : Submodule ℂ (GAf L n → ℂ), W' ≤ W →
      (∀ x : GAf L n, TrivOutside {s.v} x → ∀ f ∈ W', NG.rt L n x f ∈ W') → W' = ⊥ ∨ W' = W) :
    ∃ τ, IsLocS π.S s τ := by
  first
  | exact @_root_.GlobalTheory.blockFieldPairProjections.exists_local_component
  | exact _root_.GlobalTheory.blockFieldPairProjections.exists_local_component
  | (apply _root_.GlobalTheory.blockFieldPairProjections.exists_local_component <;> assumption)
  | (intros; apply _root_.GlobalTheory.blockFieldPairProjections.exists_local_component <;> assumption)
  | (intros; apply @_root_.GlobalTheory.blockFieldPairProjections.exists_local_component <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.blockFieldPairProjections.exists_local_component ..)

end Asm
end GlobalTheory.RowLocal

namespace GlobalTheory.RowLocal

theorem finTyp_exists_isLocS : ∀ (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (j : ℕ) (_ : RowMod D rep j) (σ : D.what₂.FT), D.what₂.isot j σ ≠ ⊥ → ∀ s : SplitPlace D.host.E, ∃ τ, IsLocS (rep σ).S s τ := by
  intro D rep j X σ hσ s
  have hB00 : X.B 0 0 = 0 := by
    have h := X.lin 0 X.C.zero_mem 0 X.C.zero_mem 0 X.C.zero_mem 1
    rw [one_smul, add_zero, one_mul] at h
    linear_combination -h
  have hne : Formalism.IndefR.principalLevelFrame.isotIn (D := D) X.ρ X.C (rep σ) ≠ ⊥ := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσ
    have hmem := (X.isot σ y).1 hy
    intro hbot
    rw [hbot, Submodule.mem_bot] at hmem
    apply hy0
    have h := X.φ_inner y y
    rw [hmem, hB00] at h
    exact inner_self_eq_zero.1 h
  obtain ⟨B', hlin, hherm, hpos, hinv⟩ := GlobalTheory.finTyp_invariant_form_of_isotIn D D.R.r X.A X.ρ X.C X.B X.lin X.herm X.pos
    X.stab X.inv (rep σ) hne
  obtain ⟨W, hWS, hW0, hst, hirr⟩ := GlobalTheory.T.exists_irreducible_subspace_trivialOutside_splitPlace D.host.E D.R.r (rep σ) B' hlin hherm hpos hinv (finTyp_fixed_finiteDimensional D rep j X σ hne) s
  exact isLocS_of_irr (rep σ) s W hWS hW0 hst hirr

end GlobalTheory.RowLocal

end
end
