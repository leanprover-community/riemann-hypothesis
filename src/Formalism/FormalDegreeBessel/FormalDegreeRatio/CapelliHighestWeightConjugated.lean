import Formalism.FormalDegreeBessel.StatementIO
import Formalism.RealPlaceAnalysis.FinalF
import Formalism.FormalDegreeBessel.FormalDegreeRatio.IOLeft

section
open Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.QuantumDeterminants

open Formalism.REAL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

abbrev IOPt {n : ℕ} (ε : Fin n → Bool) : Type := {g : Matrix (Fin n) (Fin n) ℂ // inUJ ε g}

open Classical in

def ioExt {n : ℕ} (ε : Fin n → Bool) {E : Type} [Zero E] (φ : IOPt ε → E) :
    Matrix (Fin n) (Fin n) ℂ → E :=
  fun g => if h : inUJ ε g then φ ⟨g, h⟩ else 0

section Core

variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma io_inUJ_mul {A B : Matrix (Fin n) (Fin n) ℂ} (hA : inUJ ε A) (hB : inUJ ε B) :
    inUJ ε (A * B) := by
  unfold inUJ at hA hB ⊢
  calc (A * B)ᴴ * Jm ε * (A * B) = Bᴴ * (Aᴴ * Jm ε * A) * B := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Jm ε := by rw [hA, hB]

lemma ioExt_at {φ : IOPt ε → E} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    ioExt ε φ g = φ ⟨g, hg⟩ := by
  unfold ioExt
  rw [dif_pos hg]

lemma io_smooth_congr {f f' : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, inUJ ε g → f g = f' g)
    (hf : SmoothOnGV ε f) : SmoothOnGV ε f' := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  exact ⟨U, F, hU, hgU, hF, fun g hg hgJ => (h g hgJ).symm.trans (hfF g hg hgJ)⟩

lemma io_smooth_zero : SmoothOnGV ε (fun _ : Matrix (Fin n) (Fin n) ℂ => (0 : E)) := by
  intro g₀ _
  exact ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩

lemma io_smooth_add {f f' : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f)
    (hf' : SmoothOnGV ε f') : SmoothOnGV ε (fun g => f g + f' g) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  obtain ⟨U', F', hU', hgU', hF', hfF'⟩ := hf' g₀ hg₀
  refine ⟨U ∩ U', fun g => F g + F' g, hU.inter hU', ⟨hgU, hgU'⟩,
    (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right), fun g hg hgJ => ?_⟩
  simp only [hfF g hg.1 hgJ, hfF' g hg.2 hgJ]

lemma io_smooth_smul {f : Matrix (Fin n) (Fin n) ℂ → E} (c : ℂ) (hf : SmoothOnGV ε f) :
    SmoothOnGV ε (fun g => c • f g) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U, fun g => c • F g, hU, hgU, hF.const_smul c, fun g hg hgJ => ?_⟩
  simp only [hfF g hg hgJ]

private lemma Jm_mul_self_eq_oneFormalDegreeRatio {n : ℕ} (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs <;> norm_num

private lemma Jm_conjTranspose_eq_selfFormalDegreeRatio {n : ℕ} (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  unfold Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp only [Pi.star_apply]
  split_ifs <;> simp

private lemma inUJ_exp_of_inG_formal_degree_ratio {n : ℕ} {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inG ε Y) :
    inUJ ε (NormedSpace.exp Y) := by
  unfold inG at hY
  unfold inUJ
  have hYH : Yᴴ = Jm ε * -Y * (Jm ε)⁻¹ := by
    have hJi : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv (Jm_mul_self_eq_oneFormalDegreeRatio ε)
    have h1 : Yᴴ * Jm ε * Jm ε = -(Jm ε * Y) * Jm ε := by rw [eq_neg_of_add_eq_zero_left hY]
    rw [Matrix.mul_assoc, Jm_mul_self_eq_oneFormalDegreeRatio, Matrix.mul_one] at h1
    rw [h1, hJi, Matrix.mul_neg, Matrix.neg_mul]
  have hJu : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, Jm_mul_self_eq_oneFormalDegreeRatio ε, Jm_mul_self_eq_oneFormalDegreeRatio ε⟩, rfl⟩
  have hJi : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv (Jm_mul_self_eq_oneFormalDegreeRatio ε)
  rw [← Matrix.exp_conjTranspose, hYH, Matrix.exp_conj _ _ hJu, hJi,
    Matrix.mul_assoc (Jm ε * NormedSpace.exp (-Y)) (Jm ε) (Jm ε), Jm_mul_self_eq_oneFormalDegreeRatio, Matrix.mul_one,
    Matrix.mul_assoc, ← Matrix.exp_add_of_commute _ _ (Commute.refl Y).neg_left, neg_add_cancel,
    NormedSpace.exp_zero, Matrix.mul_one]

private lemma inG_real_smul_of_inG {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    (t : ℝ) : inG ε ((t : ℂ) • X) := by
  unfold inG at hX ⊢
  have hs : star (t : ℂ) = t := Complex.conj_ofReal t
  rw [Matrix.conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]

lemma io_rd_congr {f f' : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, inUJ ε g → f g = f' g)
    {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hg : inUJ ε g) : RdV X f g = RdV X f' g := by
  unfold RdV
  congr 1
  funext t
  exact h _ (io_inUJ_mul hg (inUJ_exp_of_inG_formal_degree_ratio (inG_real_smul_of_inG hX t)))

private lemma inG_cpart1_formal_degree_ratio {n : ℕ} (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inG ε (cpart1 ε Z) := by
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp only [star_div₀, star_one, star_ofNat]
  have hJJ : ∀ M : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * M) = M := fun M => by
    rw [← Matrix.mul_assoc, Jm_mul_self_eq_oneFormalDegreeRatio, Matrix.one_mul]
  unfold inG cpart1
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Jm_conjTranspose_eq_selfFormalDegreeRatio, hs, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.mul_assoc, Jm_mul_self_eq_oneFormalDegreeRatio, Matrix.mul_one, hJJ, smul_sub]
  abel

private lemma inG_cpart2_formal_degree_ratio {n : ℕ} (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inG ε (cpart2 ε Z) := by
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  have hs : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    simp only [star_div₀, star_one, star_mul', hI, star_ofNat]
    ring
  have hJJ : ∀ M : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * M) = M := fun M => by
    rw [← Matrix.mul_assoc, Jm_mul_self_eq_oneFormalDegreeRatio, Matrix.one_mul]
  unfold inG cpart2
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Jm_conjTranspose_eq_selfFormalDegreeRatio, hs, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul,
    Matrix.mul_add, Matrix.mul_assoc, Jm_mul_self_eq_oneFormalDegreeRatio, Matrix.mul_one, hJJ, smul_add, neg_smul]
  simp only [neg_smul, one_smul, Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_assoc, Jm_mul_self_eq_oneFormalDegreeRatio,
    Matrix.mul_one]
  abel

lemma io_eab_congr {f f' : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, inUJ ε g → f g = f' g)
    (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    EabV ε a b f g = EabV ε a b f' g := by
  simp only [EabV, EcV]
  rw [io_rd_congr h (inG_cpart1_formal_degree_ratio ε _) hg, io_rd_congr h (inG_cpart2_formal_degree_ratio ε _) hg]

lemma io_eab_smooth {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f) (a b : Fin n) :
    SmoothOnGV ε (EabV ε a b f) := by
  have h1 := rdSmoothV n ε E f (cpart1 ε (Matrix.single a b 1)) hf (inG_cpart1_formal_degree_ratio ε _)
  have h2 := rdSmoothV n ε E f (cpart2 ε (Matrix.single a b 1)) hf (inG_cpart2_formal_degree_ratio ε _)
  exact io_smooth_add h1 (io_smooth_smul Complex.I h2)

lemma io_eab_lin {f f' : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f)
    (hf' : SmoothOnGV ε f') (c : ℂ) (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    EabV ε a b (fun h => f h + c • f' h) g = EabV ε a b f g + c • EabV ε a b f' g := by
  have h1 := (rdLinV n ε E f f' (cpart1 ε (Matrix.single a b 1)) (cpart1 ε (Matrix.single a b 1)) 0 c g
    hf hf' (inG_cpart1_formal_degree_ratio ε _) (inG_cpart1_formal_degree_ratio ε _) hg).2.2
  have h2 := (rdLinV n ε E f f' (cpart2 ε (Matrix.single a b 1)) (cpart2 ε (Matrix.single a b 1)) 0 c g
    hf hf' (inG_cpart2_formal_degree_ratio ε _) (inG_cpart2_formal_degree_ratio ε _) hg).2.2
  simp only [EabV, EcV]
  rw [h1, h2, smul_add, smul_add, smul_comm Complex.I c]
  abel

lemma io_eab_zero (a b : Fin n) (g : Matrix (Fin n) (Fin n) ℂ) :
    EabV ε a b (fun _ : Matrix (Fin n) (Fin n) ℂ => (0 : E)) g = 0 := by
  simp only [EabV, EcV, RdV, deriv_const, smul_zero, add_zero]

variable (ε E) in

def ioS : Submodule ℂ (IOPt ε → E) where
  carrier := {φ | SmoothOnGV ε (ioExt ε φ)}
  add_mem' {φ ψ} hφ hψ :=
    io_smooth_congr (fun g hg => by simp only [ioExt_at hg, Pi.add_apply]) (io_smooth_add hφ hψ)
  zero_mem' := io_smooth_congr (fun g hg => by simp only [ioExt_at hg, Pi.zero_apply]) io_smooth_zero
  smul_mem' c φ hφ :=
    io_smooth_congr (fun g hg => by simp only [ioExt_at hg, Pi.smul_apply]) (io_smooth_smul c hφ)

lemma io_mem_smooth (x : ioS ε E) : SmoothOnGV ε (ioExt ε (x : IOPt ε → E)) := x.2

def IORep (F : Matrix (Fin n) (Fin n) ℂ → E) (φ : IOPt ε → E) : Prop :=
  ∀ g (hg : inUJ ε g), F g = φ ⟨g, hg⟩

variable (ε) in

def ioT (a b : Fin n) (φ : IOPt ε → E) : IOPt ε → E := fun g => EabV ε a b (ioExt ε φ) g.1

lemma ioT_rep {F : Matrix (Fin n) (Fin n) ℂ → E} {φ : IOPt ε → E} (h : IORep F φ) (a b : Fin n) :
    IORep (EabV ε a b F) (ioT ε a b φ) := by
  intro g hg
  exact io_eab_congr (fun g' hg' => (h g' hg').trans (ioExt_at hg').symm) a b hg

lemma ioT_mem {φ : IOPt ε → E} (hφ : φ ∈ ioS ε E) (a b : Fin n) : ioT ε a b φ ∈ ioS ε E := by
  show SmoothOnGV ε (ioExt ε (ioT ε a b φ))
  exact io_smooth_congr (fun g hg => (ioExt_at (φ := ioT ε a b φ) hg).symm) (io_eab_smooth hφ a b)

lemma ioT_add {φ ψ : IOPt ε → E} (hφ : φ ∈ ioS ε E) (hψ : ψ ∈ ioS ε E) (a b : Fin n) :
    ioT ε a b (φ + ψ) = ioT ε a b φ + ioT ε a b ψ := by
  funext g
  show EabV ε a b (ioExt ε (φ + ψ)) g.1 = EabV ε a b (ioExt ε φ) g.1 + EabV ε a b (ioExt ε ψ) g.1
  rw [io_eab_congr (f := ioExt ε (φ + ψ)) (f' := fun h => ioExt ε φ h + (1 : ℂ) • ioExt ε ψ h)
    (fun h hh => by simp only [ioExt_at hh, Pi.add_apply, one_smul]) a b g.2,
    io_eab_lin hφ hψ 1 a b g.2, one_smul]

lemma ioT_smul {φ : IOPt ε → E} (hφ : φ ∈ ioS ε E) (c : ℂ) (a b : Fin n) :
    ioT ε a b (c • φ) = c • ioT ε a b φ := by
  funext g
  show EabV ε a b (ioExt ε (c • φ)) g.1 = c • EabV ε a b (ioExt ε φ) g.1
  rw [io_eab_congr (f := ioExt ε (c • φ))
    (f' := fun h => (fun _ : Matrix (Fin n) (Fin n) ℂ => (0 : E)) h + c • ioExt ε φ h)
    (fun h hh => by simp only [ioExt_at hh, Pi.smul_apply, zero_add]) a b g.2,
    io_eab_lin io_smooth_zero hφ c a b g.2, io_eab_zero, zero_add]

variable (ε E) in

def ioE (a b : Fin n) : Module.End ℂ (ioS ε E) where
  toFun x := ⟨ioT ε a b x.1, ioT_mem x.2 a b⟩
  map_add' x y := Subtype.ext (ioT_add x.2 y.2 a b)
  map_smul' c x := Subtype.ext (ioT_smul x.2 c a b)

lemma ioE_rep {F : Matrix (Fin n) (Fin n) ℂ → E} {x : ioS ε E} (h : IORep F x.1) (a b : Fin n) :
    IORep (EabV ε a b F) (ioE ε E a b x).1 :=
  ioT_rep h a b

lemma io_rep_ext (x : ioS ε E) : IORep (ioExt ε x.1) x.1 := by
  intro g hg
  exact ioExt_at hg

lemma io_rep_unique {F : Matrix (Fin n) (Fin n) ℂ → E} {x y : ioS ε E} (hx : IORep F x.1)
    (hy : IORep F y.1) : x = y := by
  apply Subtype.ext
  funext g
  exact (hx g.1 g.2).symm.trans (hy g.1 g.2)

lemma io_rep_mk {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f) :
    ∃ x : ioS ε E, IORep f x.1 := by
  refine ⟨⟨fun g => f g.1, ?_⟩, fun g hg => rfl⟩
  show SmoothOnGV ε (ioExt ε (fun g : IOPt ε => f g.1))
  exact io_smooth_congr (fun g hg => (ioExt_at (φ := fun g : IOPt ε => f g.1) hg).symm) hf

lemma io_rep_sum {ι : Type*} [Fintype ι] (c : ι → ℂ) {F : ι → Matrix (Fin n) (Fin n) ℂ → E}
    {x : ι → ioS ε E} (h : ∀ i, IORep (F i) (x i).1) :
    IORep (fun g => ∑ i, c i • F i g) (∑ i, c i • x i).1 := by
  intro g hg
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h i g hg]

lemma io_Tm_rep {F : Matrix (Fin n) (Fin n) ℂ → E} {x : ioS ε E} (h : IORep F x.1) (u : ℂ)
    (a b : Fin n) : IORep (Top (EabV ε) u a b F) (Tm (ioE ε E) u a b x).1 := by
  intro g hg
  simp only [Top, Tm]
  split_ifs with hab
  · simp only [LinearMap.add_apply, Module.algebraMap_end_apply, Submodule.coe_add, Submodule.coe_smul,
      Pi.add_apply, Pi.smul_apply, h g hg, ioE_rep h a b g hg]
  · simp only [LinearMap.add_apply, LinearMap.zero_apply, zero_add, ioE_rep h a b g hg]

lemma io_foldr_rep (l : List (ℂ × Fin n × Fin n)) {F : Matrix (Fin n) (Fin n) ℂ → E}
    {x : ioS ε E} (h : IORep F x.1) :
    IORep ((l.map fun p => Top (EabV ε) p.1 p.2.1 p.2.2).foldr (fun T f => T f) F)
      ((l.map fun p => Tm (ioE ε E) p.1 p.2.1 p.2.2).prod x).1 := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.foldr_nil, List.prod_nil, Module.End.one_apply]
    exact h
  | cons p l ih =>
    simp only [List.map_cons, List.foldr_cons, List.prod_cons, Module.End.mul_apply]
    exact io_Tm_rep ih _ _ _

lemma io_qminor_apply {t : ℕ} (a b : Fin t → Fin n) (u : ℂ) (x : ioS ε E) :
    qminor (ioE ε E) a b u x = ∑ σ : Equiv.Perm (Fin t), (((Equiv.Perm.sign σ : ℤ) : ℂ)) •
      ((List.ofFn fun k : Fin t => (u - ((k : ℕ) : ℂ), a (σ k), b k)).map
        fun p => Tm (ioE ε E) p.1 p.2.1 p.2.2).prod x := by
  simp only [qminor, LinearMap.sum_apply, Module.End.mul_apply, Module.End.intCast_apply,
    Int.cast_smul_eq_zsmul, List.map_ofFn, Function.comp_def]

lemma io_qminor_rep {t : ℕ} (a b : Fin t → Fin n) (u : ℂ) {F : Matrix (Fin n) (Fin n) ℂ → E}
    {x : ioS ε E} (h : IORep F x.1) :
    IORep (qminorOp (EabV ε) a b u F) (qminor (ioE ε E) a b u x).1 := by
  intro g hg
  rw [io_qminor_apply]
  refine Eq.trans ?_ (io_rep_sum (fun σ : Equiv.Perm (Fin t) => ((Equiv.Perm.sign σ : ℤ) : ℂ))
    (fun σ => io_foldr_rep (List.ofFn fun k : Fin t => (u - ((k : ℕ) : ℂ), a (σ k), b k)) h) g hg)
  simp only [qminorOp, Finset.sum_apply, Pi.smul_apply, List.map_ofFn, Function.comp_def]

variable (ε E) in
lemma io_gl : GlRel (ioE ε E) := by
  intro a b c d
  refine LinearMap.ext fun x => Subtype.ext (funext fun p => ?_)
  obtain ⟨g, hg⟩ := p
  have hF := io_rep_ext x
  have key := eabGlV n ε E (ioExt ε x.1) a b c d g (io_mem_smooth x) hg
  have r1 := ioE_rep (ioE_rep hF c d) a b g hg
  have r2 := ioE_rep (ioE_rep hF a b) c d g hg
  have r3 := ioE_rep hF a d g hg
  have r4 := ioE_rep hF c b g hg
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply]
  rw [← r1, ← r2, key]
  split_ifs <;> simp [r3, r4]

end Core

theorem capelli_central_holds : CapCentral := by
  intro n ε E _ _ f u c d g hf hg
  obtain ⟨x, hx⟩ := io_rep_mk (ε := ε) (E := E) hf
  have hq := qDetCentral (Module.End ℂ (ioS ε E)) n (ioE ε E) (io_gl ε E) u c d
  calc capelli ε u (EabV ε c d f) g
      = (qminor (ioE ε E) id id u (ioE ε E c d x) : IOPt ε → E) ⟨g, hg⟩ :=
        io_qminor_rep id id u (ioE_rep hx c d) g hg
    _ = (ioE ε E c d (qminor (ioE ε E) id id u x) : IOPt ε → E) ⟨g, hg⟩ :=
        congrArg (fun y : ioS ε E => (y : IOPt ε → E) ⟨g, hg⟩) (LinearMap.congr_fun hq x)
    _ = EabV ε c d (capelli ε u f) g := (ioE_rep (io_qminor_rep id id u hx) c d g hg).symm

theorem capelli_highest_weight_holds : CapHW := by
  intro n ε E _ _ f ν hf hHW g hg
  obtain ⟨x, hx⟩ := io_rep_mk (ε := ε) (E := E) hf
  have hW : IsHW (ioE ε E) ν x := by
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · refine Subtype.ext (funext fun p => ?_)
      obtain ⟨g', hg'⟩ := p
      calc (ioE ε E a a x : IOPt ε → E) ⟨g', hg'⟩ = EabV ε a a f g' := (ioE_rep hx a a g' hg').symm
        _ = ν a • f g' := (hHW g' hg').1 a
        _ = ν a • (x : IOPt ε → E) ⟨g', hg'⟩ := by rw [hx g' hg']
        _ = ((ν a • x : ioS ε E) : IOPt ε → E) ⟨g', hg'⟩ := rfl
    · refine Subtype.ext (funext fun p => ?_)
      obtain ⟨g', hg'⟩ := p
      calc (ioE ε E a b x : IOPt ε → E) ⟨g', hg'⟩ = EabV ε a b f g' := (ioE_rep hx a b g' hg').symm
        _ = 0 := (hHW g' hg').2 a b hab
        _ = ((0 : ioS ε E) : IOPt ε → E) ⟨g', hg'⟩ := rfl
  have hu : ∀ u : ℂ, capelli ε u f g = (∏ k : Fin n, (u - ((k : ℕ) : ℂ) + ν k)) • f g := by
    intro u
    calc capelli ε u f g = (qminor (ioE ε E) id id u x : IOPt ε → E) ⟨g, hg⟩ :=
          io_qminor_rep id id u hx g hg
      _ = (((∏ k : Fin n, (u - ((k : ℕ) : ℂ) + ν k)) • x : ioS ε E) : IOPt ε → E) ⟨g, hg⟩ :=
          congrArg (fun y : ioS ε E => (y : IOPt ε → E) ⟨g, hg⟩)
            (qDetHW (ioS ε E) n (ioE ε E) ν x (io_gl ε E) hW u)
      _ = (∏ k : Fin n, (u - ((k : ℕ) : ℂ) + ν k)) • (x : IOPt ε → E) ⟨g, hg⟩ := rfl
      _ = (∏ k : Fin n, (u - ((k : ℕ) : ℂ) + ν k)) • f g := by rw [hx g hg]
  refine ⟨hu, fun Y => ?_⟩
  rw [hu]
  congr 1
  exact Finset.prod_congr rfl fun k _ => by ring

theorem capelli_comatrix_holds : CapComatrix := by
  intro m ε E _ _ f u i l g hf hg
  obtain ⟨x, hx⟩ := io_rep_mk (ε := ε) (E := E) hf
  have hq := LinearMap.congr_fun
    (qComatrix (Module.End ℂ (ioS ε E)) m (ioE ε E) (io_gl ε E) u i l) x
  have hy : ∀ j : Fin (m + 1), IORep (qminorOp (EabV ε) (Fin.succAbove j) (Fin.succAbove i) u
      (Top (EabV ε) (u - (m : ℂ)) j l f))
      (qminor (ioE ε E) (Fin.succAbove j) (Fin.succAbove i) u (Tm (ioE ε E) (u - (m : ℂ)) j l x)).1 :=
    fun j => io_qminor_rep _ _ u (io_Tm_rep hx _ j l)
  have hs := io_rep_sum (fun j : Fin (m + 1) => ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)))) hy g hg
  have hc : (∑ j : Fin (m + 1), ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) •
      qminor (ioE ε E) (Fin.succAbove j) (Fin.succAbove i) u (Tm (ioE ε E) (u - (m : ℂ)) j l x)) =
      (if i = l then qdet (ioE ε E) u else 0) x := by
    rw [← hq]
    simp only [LinearMap.sum_apply, Module.End.mul_apply, Module.End.intCast_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [← Int.cast_smul_eq_zsmul ℂ, Int.cast_pow, Int.cast_neg, Int.cast_one]
  calc (∑ j : Fin (m + 1), ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) •
        qminorOp (EabV ε) (Fin.succAbove j) (Fin.succAbove i) u (Top (EabV ε) (u - (m : ℂ)) j l f) g)
      = ((∑ j : Fin (m + 1), ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) •
          qminor (ioE ε E) (Fin.succAbove j) (Fin.succAbove i) u (Tm (ioE ε E) (u - (m : ℂ)) j l x) :
          ioS ε E) : IOPt ε → E) ⟨g, hg⟩ := hs
    _ = (((if i = l then qdet (ioE ε E) u else 0) x : ioS ε E) : IOPt ε → E) ⟨g, hg⟩ := by rw [hc]
    _ = if i = l then capelli ε u f g else 0 := by
      split_ifs with h
      · exact (io_qminor_rep id id u hx g hg).symm
      · rfl

end Formalism.QuantumDeterminants
end
end

section
open Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.QuantumDeterminants

open Formalism.REAL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Transport

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma ioh_exp_conj (P Q X : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) (hPQ : P * Q = 1) :
    NormedSpace.exp (P * X * Q) = P * NormedSpace.exp X * Q := by
  let U : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨P, Q, hPQ, hQP⟩
  exact Matrix.exp_units_conj U X

lemma ioh_rdV (P Q X x : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E)
    (hQP : Q * P = 1) (hPQ : P * Q = 1) :
    RdV X f x = RdV (P * X * Q) (fun y => f (Q * y * P)) (P * x * Q) := by
  unfold RdV
  congr 1
  funext t
  have h1 : ((t : ℂ) • (P * X * Q)) = P * ((t : ℂ) • X) * Q := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [h1, ioh_exp_conj P Q _ hQP hPQ]
  congr 1
  have e : Q * (P * x * Q * (P * NormedSpace.exp ((t : ℂ) • X) * Q)) * P
      = (Q * P) * x * (Q * P) * NormedSpace.exp ((t : ℂ) • X) * (Q * P) := by
    simp only [Matrix.mul_assoc]
  rw [e, hQP]; simp

lemma ioh_Hinv (ε : Fin n → Bool) (H P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1)
    (hPQ : P * Q = 1) (hH : H = Pᴴ * Jm ε * P) : H⁻¹ = Q * Jm ε * Qᴴ := by
  apply Matrix.inv_eq_right_inv
  have hc : Pᴴ * Qᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hQP, Matrix.conjTranspose_one]
  calc H * (Q * Jm ε * Qᴴ) = Pᴴ * (Jm ε * ((P * Q) * (Jm ε * Qᴴ))) := by
        rw [hH]; simp only [Matrix.mul_assoc]
    _ = Pᴴ * Qᴴ := by
        rw [hPQ, Matrix.one_mul, ← Matrix.mul_assoc (Jm ε), Jm_mul_self, Matrix.one_mul]
    _ = 1 := hc

lemma ioh_conj_part (ε : Fin n → Bool) (H P Q Z : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1)
    (hPQ : P * Q = 1) (hH : H = Pᴴ * Jm ε * P) :
    P * (H⁻¹ * Zᴴ * H) * Q = Jm ε * (P * Z * Q)ᴴ * Jm ε := by
  rw [ioh_Hinv ε H P Q hQP hPQ hH, hH]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc P Q, hPQ, Matrix.one_mul, Matrix.mul_one]

lemma ioh_hpart1 (ε : Fin n → Bool) (H P Q Z : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1)
    (hPQ : P * Q = 1) (hH : H = Pᴴ * Jm ε * P) :
    P * hpart1 H Z * Q = cpart1 ε (P * Z * Q) := by
  have h := ioh_conj_part ε H P Q Z hQP hPQ hH
  unfold hpart1 cpart1
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, ← h]

lemma ioh_hpart2 (ε : Fin n → Bool) (H P Q Z : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1)
    (hPQ : P * Q = 1) (hH : H = Pᴴ * Jm ε * P) :
    P * hpart2 H Z * Q = cpart2 ε (P * Z * Q) := by
  have h := ioh_conj_part ε H P Q Z hQP hPQ hH
  unfold hpart2 cpart2
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, ← h]

lemma ioh_EabH_eq (ε : Fin n → Bool) (H P Q : Matrix (Fin n) (Fin n) ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → E) (a b : Fin n) (hQP : Q * P = 1) (hPQ : P * Q = 1)
    (hH : H = Pᴴ * Jm ε * P) (x : Matrix (Fin n) (Fin n) ℂ) :
    EabH H a b f x = EcV ε (P * Matrix.single a b 1 * Q) (fun y => f (Q * y * P)) (P * x * Q) := by
  unfold EabH EcV
  rw [ioh_rdV P Q _ x f hQP hPQ, ioh_rdV P Q (hpart2 H _) x f hQP hPQ,
    ioh_hpart1 ε H P Q _ hQP hPQ hH, ioh_hpart2 ε H P Q _ hQP hPQ hH]

lemma ioh_EabH_fun (ε : Fin n → Bool) (H P Q : Matrix (Fin n) (Fin n) ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → E) (a b : Fin n) (hQP : Q * P = 1) (hPQ : P * Q = 1)
    (hH : H = Pᴴ * Jm ε * P) :
    (fun y => EabH H a b f (Q * y * P)) =
      EcV ε (P * Matrix.single a b 1 * Q) (fun y => f (Q * y * P)) := by
  funext y
  rw [ioh_EabH_eq ε H P Q f a b hQP hPQ hH]
  congr 1
  have : P * (Q * y * P) * Q = (P * Q) * y * (P * Q) := by simp only [Matrix.mul_assoc]
  rw [this, hPQ]; simp

lemma ioh_inUJ (ε : Fin n → Bool) (H P Q g : Matrix (Fin n) (Fin n) ℂ) (hPQ : P * Q = 1)
    (hH : H = Pᴴ * Jm ε * P) (hg : inUH H g) : inUJ ε (P * g * Q) := by
  unfold inUH at hg
  unfold inUJ
  have hc : Qᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hPQ, Matrix.conjTranspose_one]
  calc (P * g * Q)ᴴ * Jm ε * (P * g * Q) = Qᴴ * (gᴴ * (Pᴴ * Jm ε * P) * g) * Q := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Qᴴ * Pᴴ * Jm ε * (P * Q) := by rw [← hH, hg, hH]; simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [hc, hPQ]; simp

lemma ioh_inUH (ε : Fin n → Bool) (H P Q x : Matrix (Fin n) (Fin n) ℂ) (hPQ : P * Q = 1)
    (hH : H = Pᴴ * Jm ε * P) (hx : inUJ ε x) : inUH H (Q * x * P) := by
  unfold inUJ at hx
  unfold inUH
  rw [hH]
  have e : (Q * x * P)ᴴ * (Pᴴ * Jm ε * P) * (Q * x * P)
      = Pᴴ * (xᴴ * ((P * Q)ᴴ * Jm ε * (P * Q)) * x) * P := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e, hPQ, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hx]

lemma ioh_single (P Q : Matrix (Fin n) (Fin n) ℂ) (a b c d : Fin n) :
    (P * Matrix.single a b (1 : ℂ) * Q) c d = P c a * Q b d := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq]

lemma ioh_smooth (ε : Fin n → Bool) (H P Q : Matrix (Fin n) (Fin n) ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → E) (hPQ : P * Q = 1)
    (hH : H = Pᴴ * Jm ε * P) (hf : SmoothOnH H f) : SmoothOnGV ε (fun x => f (Q * x * P)) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg₀U, hF, hfF⟩ := hf (Q * g₀ * P) (ioh_inUH ε H P Q g₀ hPQ hH hg₀)
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    ((LinearMap.mulLeft ℝ Q).comp (LinearMap.mulRight ℝ P)).toContinuousLinearMap
  have hL : ∀ x, L x = Q * x * P := by
    intro x; simp [L, Matrix.mul_assoc]
  refine ⟨L ⁻¹' U, fun x => F (L x), hU.preimage L.continuous, by simpa [hL] using hg₀U, ?_, ?_⟩
  · exact hF.comp L.contDiff.contDiffOn (fun x hx => hx)
  · intro x hx hxJ
    simp only [Set.mem_preimage, hL] at hx
    simp only [hL]
    exact hfF _ hx (ioh_inUH ε H P Q x hPQ hH hxJ)

end Transport

theorem conjugated_generator_transport : EabHTransport := by
  intro n ε E _ _ H P Q f a b g hQP hPQ hH hsm hg
  rw [ioh_EabH_eq ε H P Q f a b hQP hPQ hH g,
    ecSumV n ε E _ _ _ hsm (ioh_inUJ ε H P Q g hPQ hH hg)]
  simp only [ioh_single]

theorem conjugated_generator_gl_relation : EabHGl := by
  intro n ε E _ _ H P Q f a b c d g hQP hPQ hH hf hg
  have hsm := ioh_smooth ε H P Q f hPQ hH hf
  have hg' := ioh_inUJ ε H P Q g hPQ hH hg
  rw [ioh_EabH_eq ε H P Q (EabH H c d f) a b hQP hPQ hH g, ioh_EabH_fun ε H P Q f c d hQP hPQ hH,
    ioh_EabH_eq ε H P Q (EabH H a b f) c d hQP hPQ hH g, ioh_EabH_fun ε H P Q f a b hQP hPQ hH,
    vector_complexified_derivative_commutator rdLinV rdBracketV rdSmoothV ε _ _ _ _ hsm hg']
  have hQPX : ∀ X : Matrix (Fin n) (Fin n) ℂ, Q * (P * X) = X := by
    intro X; rw [← Matrix.mul_assoc, hQP, Matrix.one_mul]
  have hm : Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 =
      (if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) := by
    by_cases h1 : b = c <;> by_cases h2 : d = a
    · subst h1; subst h2; simp
    · subst h1; simp [h2]
    · subst h2; simp [h1]
    · simp [h1, h2]
  have hm2 : P * Matrix.single a b (1 : ℂ) * Q * (P * Matrix.single c d 1 * Q) -
      P * Matrix.single c d 1 * Q * (P * Matrix.single a b 1 * Q) =
      P * (Matrix.single a b (1 : ℂ) * Matrix.single c d 1 -
        Matrix.single c d 1 * Matrix.single a b 1) * Q := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hQPX]
  rw [hm2, hm, Matrix.mul_sub, Matrix.sub_mul, vector_complexified_derivative_sub rdLinV hsm hg']
  split_ifs <;> simp only [Matrix.mul_zero, Matrix.zero_mul, vector_complexified_derivative_zero, sub_zero, zero_sub,
    ioh_EabH_eq ε H P Q f _ _ hQP hPQ hH g]

section Central

variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def IOHRepr (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E))
    (Ealg : Fin n → Fin n → Module.End ℂ (ioS ε E)) : Prop :=
  ∀ (a b : Fin n) (F : Matrix (Fin n) (Fin n) ℂ → E) (x : ioS ε E), IORep F x.1 →
    IORep (Eop a b F) (Ealg a b x).1

lemma ioh_Tm_rep {Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)}
    {Ealg : Fin n → Fin n → Module.End ℂ (ioS ε E)} (hR : IOHRepr Eop Ealg)
    {F : Matrix (Fin n) (Fin n) ℂ → E} {x : ioS ε E} (h : IORep F x.1) (u : ℂ)
    (a b : Fin n) : IORep (Top Eop u a b F) (Tm Ealg u a b x).1 := by
  intro g hg
  have he := hR a b F x h g hg
  unfold Top Tm
  by_cases hab : a = b
  · rw [if_pos hab, if_pos hab, LinearMap.add_apply, Module.algebraMap_end_apply, Submodule.coe_add,
      Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, he, h g hg]
  · rw [if_neg hab, if_neg hab, zero_add, zero_add, he]

lemma ioh_foldr_rep {Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)}
    {Ealg : Fin n → Fin n → Module.End ℂ (ioS ε E)} (hR : IOHRepr Eop Ealg)
    (l : List (ℂ × Fin n × Fin n)) {F : Matrix (Fin n) (Fin n) ℂ → E}
    {x : ioS ε E} (h : IORep F x.1) :
    IORep ((l.map fun p => Top Eop p.1 p.2.1 p.2.2).foldr (fun T f => T f) F)
      ((l.map fun p => Tm Ealg p.1 p.2.1 p.2.2).prod x).1 := by
  induction l with
  | nil => simpa using h
  | cons p l ih =>
    simp only [List.map_cons, List.foldr_cons, List.prod_cons, Module.End.mul_apply]
    exact ioh_Tm_rep hR ih _ _ _

lemma ioh_qminor_apply {t : ℕ} (Ealg : Fin n → Fin n → Module.End ℂ (ioS ε E))
    (a b : Fin t → Fin n) (u : ℂ) (x : ioS ε E) :
    qminor Ealg a b u x = ∑ σ : Equiv.Perm (Fin t), (((Equiv.Perm.sign σ : ℤ) : ℂ)) •
      ((List.ofFn fun k : Fin t => (u - ((k : ℕ) : ℂ), a (σ k), b k)).map
        fun p => Tm Ealg p.1 p.2.1 p.2.2).prod x := by
  unfold qminor
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Module.End.mul_apply, Module.End.intCast_apply, List.map_ofFn, Int.cast_smul_eq_zsmul]
  rfl

lemma ioh_qminor_rep {Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)}
    {Ealg : Fin n → Fin n → Module.End ℂ (ioS ε E)} (hR : IOHRepr Eop Ealg)
    {t : ℕ} (a b : Fin t → Fin n) (u : ℂ) {F : Matrix (Fin n) (Fin n) ℂ → E}
    {x : ioS ε E} (h : IORep F x.1) :
    IORep (qminorOp Eop a b u F) (qminor Ealg a b u x).1 := by
  intro g hg
  rw [ioh_qminor_apply]
  have hs := io_rep_sum (fun σ : Equiv.Perm (Fin t) => (((Equiv.Perm.sign σ : ℤ) : ℂ)))
    (fun σ => ioh_foldr_rep hR (List.ofFn fun k : Fin t => (u - ((k : ℕ) : ℂ), a (σ k), b k)) h) g hg
  rw [← hs]
  unfold qminorOp
  simp only [Finset.sum_apply, Pi.smul_apply, List.map_ofFn]
  rfl

variable (ε E) in

def iohE (P Q : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) : Module.End ℂ (ioS ε E) :=
  ∑ c, ∑ d, (P c a * Q b d) • ioE ε E c d

lemma ioh_repr (P Q : Matrix (Fin n) (Fin n) ℂ) :
    IOHRepr (fun a b => EcV ε (P * Matrix.single a b 1 * Q)) (iohE ε E P Q) := by
  intro a b F x h g hg
  have hF : SmoothOnGV ε F :=
    io_smooth_congr (fun g' hg' => (io_rep_ext x g' hg').trans (h g' hg').symm) (io_mem_smooth x)
  show EcV ε (P * Matrix.single a b 1 * Q) F g =
    (((∑ c, ∑ d, (P c a * Q b d) • ioE ε E c d) x : ioS ε E) : IOPt ε → E) ⟨g, hg⟩
  rw [ecSumV n ε E F _ g hF hg]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum,
    Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, ioh_single]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [ioE_rep h c d g hg]

lemma ioh_gl (hAd : GlRelAd) (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) :
    GlRel (iohE ε E P Q) :=
  hAd (Module.End ℂ (ioS ε E)) n (ioE ε E) P Q (io_gl ε E) hQP

end Central

section Conj

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma ioh_PQ (P Q y : Matrix (Fin n) (Fin n) ℂ) (hPQ : P * Q = 1) : P * (Q * y * P) * Q = y := by
  have : P * (Q * y * P) * Q = (P * Q) * y * (P * Q) := by simp only [Matrix.mul_assoc]
  rw [this, hPQ]; simp

lemma ioh_QP (P Q y : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) : Q * (P * y * Q) * P = y := by
  have : Q * (P * y * Q) * P = (Q * P) * y * (Q * P) := by simp only [Matrix.mul_assoc]
  rw [this, hQP]; simp

lemma ioh_Top (ε : Fin n → Bool) (H P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1)
    (hPQ : P * Q = 1) (hH : H = Pᴴ * Jm ε * P) (u : ℂ) (a b : Fin n)
    (R : Matrix (Fin n) (Fin n) ℂ → E) :
    Top (EabH H) u a b (fun x => R (P * x * Q)) =
      fun x => Top (fun a b => EcV ε (P * Matrix.single a b 1 * Q)) u a b R (P * x * Q) := by
  funext x
  unfold Top
  rw [ioh_EabH_eq ε H P Q _ a b hQP hPQ hH x]
  have : (fun y => (fun x => R (P * x * Q)) (Q * y * P)) = R := by
    funext y; simp only [ioh_PQ P Q y hPQ]
  rw [this]

lemma ioh_foldr (ε : Fin n → Bool) (H P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1)
    (hPQ : P * Q = 1) (hH : H = Pᴴ * Jm ε * P) (l : List (ℂ × Fin n × Fin n))
    (G : Matrix (Fin n) (Fin n) ℂ → E) :
    (l.map fun p => Top (EabH H) p.1 p.2.1 p.2.2).foldr (fun T h => T h) G =
      fun x => (l.map fun p => Top (fun a b => EcV ε (P * Matrix.single a b 1 * Q)) p.1 p.2.1 p.2.2).foldr
        (fun T h => T h) (fun y => G (Q * y * P)) (P * x * Q) := by
  induction l with
  | nil =>
    funext x
    simp only [List.map_nil, List.foldr_nil, ioh_QP P Q x hQP]
  | cons p l ih =>
    simp only [List.map_cons, List.foldr_cons]
    rw [ih, ioh_Top ε H P Q hQP hPQ hH]

lemma ioh_qminor (ε : Fin n → Bool) (H P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1)
    (hPQ : P * Q = 1) (hH : H = Pᴴ * Jm ε * P) {t : ℕ} (α β : Fin t → Fin n) (u : ℂ)
    (G : Matrix (Fin n) (Fin n) ℂ → E) (x : Matrix (Fin n) (Fin n) ℂ) :
    qminorOp (EabH H) α β u G x =
      qminorOp (fun a b => EcV ε (P * Matrix.single a b 1 * Q)) α β u (fun y => G (Q * y * P))
        (P * x * Q) := by
  unfold qminorOp
  simp only [Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have e1 : ∀ (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)),
      (List.ofFn fun k : Fin t => Top Eop (u - ((k : ℕ) : ℂ)) (α (σ k)) (β k)) =
        (List.ofFn fun k : Fin t => (u - ((k : ℕ) : ℂ), α (σ k), β k)).map
          fun p => Top Eop p.1 p.2.1 p.2.2 := by
    intro Eop; rw [List.map_ofFn]; rfl
  rw [e1, e1, ioh_foldr ε H P Q hQP hPQ hH]

lemma ioh_qminor_fun (ε : Fin n → Bool) (H P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1)
    (hPQ : P * Q = 1) (hH : H = Pᴴ * Jm ε * P) {t : ℕ} (α β : Fin t → Fin n) (u : ℂ)
    (G : Matrix (Fin n) (Fin n) ℂ → E) :
    (fun y => qminorOp (EabH H) α β u G (Q * y * P)) =
      qminorOp (fun a b => EcV ε (P * Matrix.single a b 1 * Q)) α β u (fun y => G (Q * y * P)) := by
  funext y
  rw [ioh_qminor ε H P Q hQP hPQ hH, ioh_PQ P Q y hPQ]

end Conj

theorem capCentralH_of (hAd : GlRelAd) : CapCentralH := by
  intro n ε E _ _ H P Q f u c d g hQP hPQ hH hf hg
  have hsm := ioh_smooth ε H P Q f hPQ hH hf
  have hg' := ioh_inUJ ε H P Q g hPQ hH hg
  obtain ⟨x, hx⟩ := io_rep_mk hsm
  have hR := ioh_repr (ε := ε) (E := E) P Q
  unfold capelliH qdetOp
  rw [ioh_qminor ε H P Q hQP hPQ hH, ioh_EabH_fun ε H P Q f c d hQP hPQ hH,
    ioh_EabH_eq ε H P Q _ c d hQP hPQ hH g, ioh_qminor_fun ε H P Q hQP hPQ hH]
  have h1 := ioh_qminor_rep hR id id u (hR c d _ x hx) _ hg'
  have h2 := hR c d _ _ (ioh_qminor_rep hR id id u hx) _ hg'
  have hc := qDetCentral (Module.End ℂ (ioS ε E)) n (iohE ε E P Q) (ioh_gl hAd P Q hQP) u c d
  dsimp only at h1 h2
  rw [h1, h2]
  unfold qdet at hc
  exact congrArg (fun T : Module.End ℂ (ioS ε E) => (T x).1 ⟨_, hg'⟩) hc

theorem capHWH_of (hAd : GlRelAd) : CapHWH := by
  intro n ε E _ _ H P Q f ν hQP hPQ hH hf hhw g hg u
  have hsm := ioh_smooth ε H P Q f hPQ hH hf
  have hg' := ioh_inUJ ε H P Q g hPQ hH hg
  obtain ⟨x, hx⟩ := io_rep_mk hsm
  have hR := ioh_repr (ε := ε) (E := E) P Q
  have hEW : ∀ a b y, EcV ε (P * Matrix.single a b 1 * Q) (fun y => f (Q * y * P)) y =
      EabH H a b f (Q * y * P) := fun a b y =>
    (congrFun (ioh_EabH_fun ε H P Q f a b hQP hPQ hH) y).symm
  have hHW : IsHW (iohE ε E P Q) ν x := by
    refine ⟨fun a => io_rep_unique (hR a a _ x hx) (fun g' hg' => ?_),
      fun a b hab => io_rep_unique (hR a b _ x hx) (fun g' hg' => ?_)⟩
    · show EcV ε (P * Matrix.single a a 1 * Q) (fun y => f (Q * y * P)) g' = _
      rw [hEW, (hhw _ (ioh_inUH ε H P Q g' hPQ hH hg')).1 a, Submodule.coe_smul,
        Pi.smul_apply, ← hx g' hg']
    · show EcV ε (P * Matrix.single a b 1 * Q) (fun y => f (Q * y * P)) g' = _
      rw [hEW, (hhw _ (ioh_inUH ε H P Q g' hPQ hH hg')).2 a b hab]; rfl
  have h1 := ioh_qminor_rep hR id id u hx _ hg'
  have h2 := qDetHW (ioS ε E) n (iohE ε E P Q) ν x (ioh_gl hAd P Q hQP) hHW u
  unfold capelliH qdetOp
  rw [ioh_qminor ε H P Q hQP hPQ hH, h1]
  unfold qdet at h2
  rw [h2]
  show (∏ k : Fin n, (u - ((k : ℕ) : ℂ) + ν k)) • x.1 ⟨_, hg'⟩ = _
  rw [← hx _ hg']
  show _ • f (Q * (P * g * Q) * P) = _
  rw [ioh_QP P Q g hQP]

theorem capelli_central_conjugated : CapCentralH := capCentralH_of gl_relation_adjoint_holds

theorem capelli_highest_weight_conjugated : CapHWH := capHWH_of gl_relation_adjoint_holds

end Formalism.QuantumDeterminants
end
end
