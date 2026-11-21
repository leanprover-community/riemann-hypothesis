import Formalism.HermitianCurvature.StatementQ
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Formalism.FormalDegreeBessel.FormalDegreeRatio.CapelliHighestWeightConjugated

section
open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.Q.TInvW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def blk {k r : ℕ} (i : Fin (r + 1)) (g : Mx k r) : Matrix (Fin (mdim k r i)) (Fin (mdim k r i)) ℂ :=
  fun a b => g (posL k r i a) (posL k r i b)

def StepS : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)), inWb k r z →
    (1 : Mx k r) ∈ Slev k r z i ∧ ∀ s ∈ Slev k r z i, s ∈ Glev k r i ∧ s *ᵥ fvec k r z i = fvec k r z i

def StepGrp : Prop :=
  ∀ (k r : ℕ) (i : Fin (r + 1)), ∀ g ∈ Glev k r i, ∀ h ∈ Glev k r i, g * h ∈ Glev k r i

def StepVec : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)), inWb k r z → inWb k r z' →
    (∀ s ∈ Slev k r z i, ∀ g : Mx k r, yv k r z i (s * g) = yv k r z i g ∧ ybv k r z i (s * g) = ybv k r z i g) ∧
    ∀ s' ∈ Slev k r z' i,
      blk i s' * blk i s'⁻¹ = 1 ∧ blk i s'⁻¹ * blk i s' = 1 ∧
      blk i s' *ᵥ xv k r z' i = xv k r z' i ∧ xbv k r z' i ᵥ* blk i s'⁻¹ = xbv k r z' i ∧
      ∀ g ∈ Glev k r i, yv k r z i g = blk i s' *ᵥ yv k r z i (g * s') ∧
        ybv k r z i g = ybv k r z i (g * s') ᵥ* blk i s'⁻¹

def StepCongr : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r))
    (a b : Fin (mdim k r i)) (f f' : Mx k r → E) (g : Mx k r), IsOpen D → g ∈ Glev k r i ∩ D →
    (∀ x ∈ Glev k r i ∩ D, f x = f' x) →
    EH k r (posL k r i a) (posL k r i b) f g = EH k r (posL k r i a) (posL k r i b) f' g

def StepRight : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r))
    (a b : Fin (mdim k r i)) (f : Mx k r → E) (s' g : Mx k r), IsOpen D → SmoothLev k r i D f →
    s' ∈ Glev k r i → g ∈ Glev k r i → g * s' ∈ D →
    EH k r (posL k r i a) (posL k r i b) (fun x => f (x * s')) g =
      ∑ c, ∑ d, (blk i s'⁻¹ c a * blk i s' b d) • EH k r (posL k r i c) (posL k r i d) f (g * s')

def StepRSm : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r))
    (f : Mx k r → E) (s' : Mx k r), s' ∈ Glev k r i → (∀ g ∈ Glev k r i ∩ D, g * s' ∈ D) →
    SmoothLev k r i D f → SmoothLev k r i D (fun x => f (x * s'))

section Alg

variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}

lemma tm_inter (E E' : Fin n → Fin n → A) (R : A) (h : ∀ a b, E a b * R = R * E' a b) (u : ℂ)
    (a b : Fin n) : Tm E u a b * R = R * Tm E' u a b := by
  unfold Tm
  rw [add_mul, mul_add, h]
  congr 1
  split_ifs
  · exact Algebra.commutes u R
  · simp

lemma prod_inter (E E' : Fin n → Fin n → A) (R : A) (h : ∀ a b, E a b * R = R * E' a b)
    (l : List (ℂ × Fin n × Fin n)) :
    (l.map fun p => Tm E p.1 p.2.1 p.2.2).prod * R = R * (l.map fun p => Tm E' p.1 p.2.1 p.2.2).prod := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [mul_assoc, ih, ← mul_assoc, tm_inter E E' R h, mul_assoc]

lemma qminor_inter (E E' : Fin n → Fin n → A) (R : A) (h : ∀ a b, E a b * R = R * E' a b)
    {t : ℕ} (α β : Fin t → Fin n) (u : ℂ) : qminor E α β u * R = R * qminor E' α β u := by
  have key : ∀ σ : Equiv.Perm (Fin t),
      (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (α (σ k)) (β k)).prod * R =
        R * (List.ofFn fun k : Fin t => Tm E' (u - (k : ℂ)) (α (σ k)) (β k)).prod := by
    intro σ
    have hl := prod_inter E E' R h (List.ofFn fun k : Fin t => (u - (k : ℂ), α (σ k), β k))
    simpa [List.map_ofFn, Function.comp_def] using hl
  unfold qminor
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_assoc, key σ, ← mul_assoc, ← mul_assoc, (Int.cast_commute _ R).eq]

lemma chatA_inter (E E' : Fin n → Fin n → A) (R : A) (h : ∀ a b, E a b * R = R * E' a b) (u : ℂ)
    (a β : Fin n → ℂ) : chatA E u a β * R = R * chatA E' u a β := by
  unfold chatA
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, qminor_inter E E' R h]

lemma second_capelli_minor_intertwines (E E' : Fin n → Fin n → A) (R : A) (h : ∀ a b, E a b * R = R * E' a b) (u : ℂ)
    (a a' β β' : Fin n → ℂ) : chat2A E u a a' β β' * R = R * chat2A E' u a a' β β' := by
  unfold chat2A
  simp only [Finset.sum_mul, Finset.mul_sum, ite_mul, mul_ite, zero_mul, mul_zero, smul_mul_assoc,
    mul_smul_comm, qminor_inter E E' R h]

lemma qdet_inter (E E' : Fin n → Fin n → A) (R : A) (h : ∀ a b, E a b * R = R * E' a b) (u : ℂ) :
    qdet E u * R = R * qdet E' u := qminor_inter E E' R h id id u

end Alg

section Model

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)}

abbrev Pt (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)) : Type := {g : Mx k r // g ∈ Glev k r i ∩ D}

open Classical in

def ext (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)) (φ : Pt k r i D → E) : Mx k r → E :=
  fun g => if h : g ∈ Glev k r i ∩ D then φ ⟨g, h⟩ else 0

lemma ext_at {φ : Pt k r i D → E} {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) : ext k r i D φ g = φ ⟨g, hg⟩ := by
  unfold ext
  rw [dif_pos hg]

lemma lev_congr (hD : IsOpen D) {f f' : Mx k r → E} (h : ∀ g ∈ Glev k r i ∩ D, f g = f' g)
    (hf : SmoothLev k r i D f) : SmoothLev k r i D f' := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U ∩ D, F, hU.inter hD, ⟨hgU, hg₀.2⟩, hF.mono Set.inter_subset_left, fun g hg hgG => ?_⟩
  rw [← h g ⟨hgG, hg.2⟩, hfF g hg.1 hgG]

lemma lev_zero : SmoothLev k r i D (fun _ : Mx k r => (0 : E)) := fun _ _ => ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

lemma lev_add {f f' : Mx k r → E} (hf : SmoothLev k r i D f) (hf' : SmoothLev k r i D f') :
    SmoothLev k r i D (fun g => f g + f' g) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  obtain ⟨U', F', hU', hgU', hF', hfF'⟩ := hf' g₀ hg₀
  refine ⟨U ∩ U', fun g => F g + F' g, hU.inter hU', ⟨hgU, hgU'⟩,
    (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right), fun g hg hgG => ?_⟩
  show f g + f' g = F g + F' g
  rw [hfF g hg.1 hgG, hfF' g hg.2 hgG]

lemma lev_smul {f : Mx k r → E} (c : ℂ) (hf : SmoothLev k r i D f) :
    SmoothLev k r i D (fun g => c • f g) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U, fun g => c • F g, hU, hgU, hF.const_smul c, fun g hg hgG => ?_⟩
  show c • f g = c • F g
  rw [hfF g hg hgG]

variable (E k r i D) in

def Sm : Submodule ℂ (Pt k r i D → E) where
  carrier := {φ | SmoothLev k r i D (ext k r i D φ)}
  add_mem' {φ ψ} hφ hψ := by
    have e : ext k r i D (φ + ψ) = fun g => ext k r i D φ g + ext k r i D ψ g := by
      funext g; unfold ext; split_ifs <;> simp
    show SmoothLev k r i D (ext k r i D (φ + ψ))
    rw [e]; exact lev_add hφ hψ
  zero_mem' := by
    have e : ext k r i D (0 : Pt k r i D → E) = fun _ => 0 := by
      funext g; unfold ext; split_ifs <;> simp
    show SmoothLev k r i D (ext k r i D (0 : Pt k r i D → E))
    rw [e]; exact lev_zero
  smul_mem' c φ hφ := by
    have e : ext k r i D (c • φ) = fun g => c • ext k r i D φ g := by
      funext g; unfold ext; split_ifs <;> simp
    show SmoothLev k r i D (ext k r i D (c • φ))
    rw [e]; exact lev_smul c hφ

def Rep (F : Mx k r → E) (φ : Pt k r i D → E) : Prop :=
  ∀ g (hg : g ∈ Glev k r i ∩ D), F g = φ ⟨g, hg⟩

lemma rep_ext (φ : Pt k r i D → E) : Rep (ext k r i D φ) φ := fun _ hg => ext_at hg

lemma posL_inj {a b : Fin (mdim k r i)} (h : posL k r i a = posL k r i b) : a = b := by
  unfold posL at h
  have h2 := congrArg Fin.val h
  simp only at h2
  exact Fin.ext (by omega)

def Tf (a b : Fin (mdim k r i)) (φ : Pt k r i D → E) : Pt k r i D → E :=
  fun p => EH k r (posL k r i a) (posL k r i b) (ext k r i D φ) p.1

lemma eh_zero (a b : Fin (2 * r + k + 1)) (g : Mx k r) :
    EH k r a b (fun _ : Mx k r => (0 : E)) g = 0 := by
  simp [EabH, RdV]

lemma rep_sum {ι : Type*} [Fintype ι] (c : ι → ℂ) {F : ι → Mx k r → E}
    {x : ι → Sm E k r i D} (h : ∀ j, Rep (F j) (x j).1) :
    Rep (fun g => ∑ j, c j • F j g) (∑ j, c j • x j).1 := by
  intro g hg
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [h j g hg]

section Ops

variable (hP : EabPres) (hC : StepCongr) (hD : IsOpen D)
include hP hC hD

lemma Tf_mem {φ : Pt k r i D → E} (hφ : φ ∈ Sm E k r i D) (a b : Fin (mdim k r i)) :
    Tf a b φ ∈ Sm E k r i D := by
  have hφ' : SmoothLev k r i D (ext k r i D φ) := hφ
  have h1 := (hP E k r (fun _ => 0) i D a b (ext k r i D φ) (ext k r i D φ) 0 hD hφ' hφ').1
  show SmoothLev k r i D (ext k r i D (Tf a b φ))
  exact lev_congr hD (fun g hg => (ext_at (φ := Tf a b φ) hg).symm) h1

lemma Tf_add {φ ψ : Pt k r i D → E} (hφ : φ ∈ Sm E k r i D) (hψ : ψ ∈ Sm E k r i D)
    (a b : Fin (mdim k r i)) : Tf a b (φ + ψ) = Tf a b φ + Tf a b ψ := by
  have hφ' : SmoothLev k r i D (ext k r i D φ) := hφ
  have hψ' : SmoothLev k r i D (ext k r i D ψ) := hψ
  funext p
  have e : ext k r i D (φ + ψ) = fun x => ext k r i D φ x + (1 : ℂ) • ext k r i D ψ x := by
    funext g; unfold ext; split_ifs <;> simp
  have h3 := (hP E k r (fun _ => 0) i D a b (ext k r i D φ) (ext k r i D ψ) 1 hD hφ' hψ').2.2 p.1 p.2
  show EH k r (posL k r i a) (posL k r i b) (ext k r i D (φ + ψ)) p.1 =
    EH k r (posL k r i a) (posL k r i b) (ext k r i D φ) p.1 + EH k r (posL k r i a) (posL k r i b) (ext k r i D ψ) p.1
  rw [e, h3, one_smul]

lemma Tf_smul {φ : Pt k r i D → E} (hφ : φ ∈ Sm E k r i D) (c : ℂ)
    (a b : Fin (mdim k r i)) : Tf a b (c • φ) = c • Tf a b φ := by
  have hφ' : SmoothLev k r i D (ext k r i D φ) := hφ
  funext p
  have e : ext k r i D (c • φ) = fun x => (0 : E) + c • ext k r i D φ x := by
    funext g; unfold ext; split_ifs <;> simp
  have h3 := (hP E k r (fun _ => 0) i D a b (fun _ => (0 : E)) (ext k r i D φ) c hD lev_zero hφ').2.2 p.1 p.2
  show EH k r (posL k r i a) (posL k r i b) (ext k r i D (c • φ)) p.1 =
    c • EH k r (posL k r i a) (posL k r i b) (ext k r i D φ) p.1
  rw [e, h3, eh_zero, zero_add]

def Ealg (a b : Fin (mdim k r i)) : Module.End ℂ (Sm E k r i D) where
  toFun x := ⟨Tf a b x.1, Tf_mem hP hC hD x.2 a b⟩
  map_add' x y := Subtype.ext (Tf_add hP hC hD x.2 y.2 a b)
  map_smul' c x := Subtype.ext (Tf_smul hP hC hD x.2 c a b)

lemma E_rep {F : Mx k r → E} {x : Sm E k r i D} (h : Rep F x.1) (a b : Fin (mdim k r i)) :
    Rep (EH k r (posL k r i a) (posL k r i b) F) (Ealg hP hC hD a b x).1 := by
  intro g hg
  show EH k r (posL k r i a) (posL k r i b) F g = EH k r (posL k r i a) (posL k r i b) (ext k r i D x.1) g
  exact hC E k r i D a b F (ext k r i D x.1) g hD hg (fun y hy => by rw [h y hy, ext_at hy])

lemma Top_rep {F : Mx k r → E} {x : Sm E k r i D} (h : Rep F x.1) (u : ℂ)
    (a b : Fin (mdim k r i)) :
    Rep (Formalism.QuantumDeterminants.Top (EH k r) u (posL k r i a) (posL k r i b) F) (Tm (Ealg hP hC hD) u a b x).1 := by
  intro g hg
  have h2 := E_rep hP hC hD h a b g hg
  by_cases hab : a = b
  · subst hab
    simp [Formalism.QuantumDeterminants.Top, Tm, h g hg, h2]
  · have hne : posL k r i a ≠ posL k r i b := fun e => hab (posL_inj e)
    simp [Formalism.QuantumDeterminants.Top, Tm, hab, hne, h2]

lemma foldr_rep (l : List (ℂ × Fin (mdim k r i) × Fin (mdim k r i))) {F : Mx k r → E}
    {x : Sm E k r i D} (h : Rep F x.1) :
    Rep ((l.map fun p => Formalism.QuantumDeterminants.Top (EH k r) p.1 (posL k r i p.2.1) (posL k r i p.2.2)).foldr (fun T f => T f) F)
      ((l.map fun p => Tm (Ealg hP hC hD) p.1 p.2.1 p.2.2).prod x).1 := by
  induction l with
  | nil => simpa using h
  | cons p l ih =>
    simp only [List.map_cons, List.foldr_cons, List.prod_cons]
    exact Top_rep hP hC hD ih p.1 p.2.1 p.2.2

lemma qminor_apply {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (u : ℂ) (x : Sm E k r i D) :
    qminor (Ealg hP hC hD) a b u x = ∑ σ : Equiv.Perm (Fin t), (((Equiv.Perm.sign σ : ℤ) : ℂ)) •
      ((List.ofFn fun k : Fin t => (u - ((k : ℕ) : ℂ), a (σ k), b k)).map
        fun p => Tm (Ealg hP hC hD) p.1 p.2.1 p.2.2).prod x := by
  unfold qminor
  simp [LinearMap.sum_apply, List.map_ofFn, Function.comp_def, Int.cast_smul_eq_zsmul]

lemma qminor_rep {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (u : ℂ) {F : Mx k r → E}
    {x : Sm E k r i D} (h : Rep F x.1) :
    Rep (qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) u F) (qminor (Ealg hP hC hD) a b u x).1 := by
  intro g hg
  rw [qminor_apply hP hC hD a b u x]
  unfold qminorOp
  simp only [Finset.sum_apply, Pi.smul_apply, Submodule.coe_sum, Submodule.coe_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have hf := foldr_rep hP hC hD (List.ofFn fun k : Fin t => (u - ((k : ℕ) : ℂ), a (σ k), b k)) h g hg
  simpa [List.map_ofFn, Function.comp_def] using hf

lemma chat_rep (u : ℂ) (a β : Mx k r → Fin (mdim k r i) → ℂ) {F : Mx k r → E}
    {x : Sm E k r i D} (h : Rep F x.1) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    chatL (EH k r) (posL k r i) u a β F g = (chatA (Ealg hP hC hD) u (a g) (β g) x).1 ⟨g, hg⟩ := by
  unfold chatL chatA
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [qminor_rep hP hC hD (skip1 i) (skip1 j) u h g hg]

lemma second_capelli_minor_represents (u : ℂ) (a a' β β' : Mx k r → Fin (mdim k r i) → ℂ) {F : Mx k r → E}
    {x : Sm E k r i D} (h : Rep F x.1) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    chat2L (EH k r) (posL k r i) u a a' β β' F g =
      (chat2A (Ealg hP hC hD) u (a g) (a' g) (β g) (β' g) x).1 ⟨g, hg⟩ := by
  unfold chat2L chat2A
  simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ =>
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  split_ifs
  · simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply]
    rw [qminor_rep hP hC hD (skip2 i i') (skip2 j j') u h g hg]
  · simp

lemma qdet_rep (u : ℂ) {F : Mx k r → E} {x : Sm E k r i D} (h : Rep F x.1) (g : Mx k r)
    (hg : g ∈ Glev k r i ∩ D) :
    capL k r i u F g = (qdet (Ealg hP hC hD) u x).1 ⟨g, hg⟩ := qminor_rep hP hC hD id id u h g hg

variable (hG : EabGlLev) in
include hG in
lemma Ealg_gl : GlRel (Ealg (E := E) (i := i) hP hC hD) := by
  intro a b c d
  apply LinearMap.ext; intro x
  apply Subtype.ext; funext p
  obtain ⟨g, hg⟩ := p
  have r0 : Rep (ext k r i D x.1) x.1 := rep_ext x.1
  have hab := E_rep hP hC hD (E_rep hP hC hD r0 c d) a b g hg
  have hcd := E_rep hP hC hD (E_rep hP hC hD r0 a b) c d g hg
  have had := E_rep hP hC hD r0 a d g hg
  have hcb := E_rep hP hC hD r0 c b g hg
  have key := hG E k r i D a b c d (ext k r i D x.1) hD x.2 g hg
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply]
  rw [← hab, ← hcd, key]
  split_ifs <;> simp [had, hcb]

variable {s' : Mx k r} (hs' : ∀ g ∈ Glev k r i ∩ D, g * s' ∈ Glev k r i ∩ D)

def Rf (φ : Pt k r i D → E) : Pt k r i D → E := fun p => φ ⟨p.1 * s', hs' p.1 p.2⟩

variable (hRS : StepRSm) (hs'G : s' ∈ Glev k r i)
include hRS hs'G

lemma Rf_mem {φ : Pt k r i D → E} (hφ : φ ∈ Sm E k r i D) : Rf hs' φ ∈ Sm E k r i D := by
  have hφ' : SmoothLev k r i D (ext k r i D φ) := hφ
  have h1 := hRS E k r i D (ext k r i D φ) s' hs'G (fun g hg => (hs' g hg).2) hφ'
  show SmoothLev k r i D (ext k r i D (Rf hs' φ))
  refine lev_congr hD (fun g hg => ?_) h1
  show ext k r i D φ (g * s') = ext k r i D (Rf hs' φ) g
  rw [ext_at hg, ext_at (hs' g hg)]
  rfl

def RL : Module.End ℂ (Sm E k r i D) where
  toFun x := ⟨Rf hs' x.1, Rf_mem hP hC hD hs' hRS hs'G x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (hRt : StepRight) in
include hRt in
lemma RL_inter (a b : Fin (mdim k r i)) :
    Ealg (E := E) hP hC hD a b * RL (E := E) hP hC hD hs' hRS hs'G =
      RL (E := E) hP hC hD hs' hRS hs'G * Econj (Ealg (E := E) hP hC hD) (blk i s'⁻¹) (blk i s') a b := by
  apply LinearMap.ext; intro x
  apply Subtype.ext; funext p
  obtain ⟨g, hg⟩ := p
  have hcon := hC E k r i D a b (ext k r i D (Rf hs' x.1)) (fun y => ext k r i D x.1 (y * s')) g hD hg
    (fun y hy => by
      show ext k r i D (Rf hs' x.1) y = ext k r i D x.1 (y * s')
      rw [ext_at hy, ext_at (hs' y hy)]
      rfl)
  have hR := hRt E k r i D a b (ext k r i D x.1) s' g hD x.2 hs'G hg.1 (hs' g hg).2
  show EH k r (posL k r i a) (posL k r i b) (ext k r i D (Rf hs' x.1)) g =
    (Econj (Ealg (E := E) hP hC hD) (blk i s'⁻¹) (blk i s') a b x).1 ⟨g * s', hs' g hg⟩
  rw [hcon, hR]
  simp only [Econj, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.smul_apply]
  rfl

lemma RL_apply (M M' : Module.End ℂ (Sm E k r i D)) (hM : M * RL (E := E) hP hC hD hs' hRS hs'G = RL (E := E) hP hC hD hs' hRS hs'G * M')
    (x : Sm E k r i D) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    (M (RL hP hC hD hs' hRS hs'G x)).1 ⟨g, hg⟩ = (M' x).1 ⟨g * s', hs' g hg⟩ := congrArg (fun T : Module.End ℂ (Sm E k r i D) => (T x).1 ⟨g, hg⟩) hM

end Ops

end Model

lemma tl00 {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (i : Fin (r + 1)) (Y : ℂ) (f : Mx k r → E) :
    tL k r z z' i Y 0 0 f = capL k r i (uC k r i Y) f := rfl

lemma tl01 {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (i : Fin (r + 1)) (Y : ℂ) (f : Mx k r → E) :
    tL k r z z' i Y 0 1 f =
      -(chatL (EH k r) (posL k r i) (uC k r i Y - 1) (fun _ => xv k r z' i) (ybv k r z i) f) := rfl

lemma tl10 {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (i : Fin (r + 1)) (Y : ℂ) (f : Mx k r → E) :
    tL k r z z' i Y 1 0 f =
      -(chatL (EH k r) (posL k r i) (uC k r i Y) (yv k r z i) (fun _ => xbv k r z' i) f) := rfl

lemma tl11 {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (i : Fin (r + 1)) (Y : ℂ) (f : Mx k r → E) :
    tL k r z z' i Y 1 1 f =
      -(chat2L (EH k r) (posL k r i) (uC k r i Y - 1) (yv k r z i) (fun _ => xv k r z' i)
        (ybv k r z i) (fun _ => xbv k r z' i) f) := rfl

lemma left_step (hL : QMinorLeftH) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ)
    (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (Y : ℂ) (p q : Fin 2) (F : Mx k r → E) (s g : Mx k r)
    (hy : yv k r z i (s * g) = yv k r z i g) (hyb : ybv k r z i (s * g) = ybv k r z i g) :
    tL k r z z' i Y p q (fun x => F (s * x)) g = tL k r z z' i Y p q F (s * g) := by
  have hq : ∀ {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ),
      qminorOp (EH k r) a b u (fun x => F (s * x)) g = qminorOp (EH k r) a b u F (s * g) := by
    intro t a b u
    exact congrFun (hL E (2 * r + k + 1) t (Hpk k r) F a b u s) g
  match p, q with
  | 0, 0 =>
    rw [tl00, tl00]
    exact hq _ _ _
  | 0, 1 =>
    rw [tl01, tl01]
    simp only [Pi.neg_apply, chatL, hq, hyb]
  | 1, 0 =>
    rw [tl10, tl10]
    simp only [Pi.neg_apply, chatL, hq, hy]
  | 1, 1 =>
    rw [tl11, tl11]
    simp only [Pi.neg_apply, chat2L, hq, hy, hyb]

theorem tInvariant_of_contractions (hCC : ContractionsCovariant) (hP : EabPres) (hG : EabGlLev) (hL : QMinorLeftH)
    (hS : StepS) (hGr : StepGrp) (hV : StepVec) (hC : StepCongr) (hRt : StepRight) (hRS : StepRSm) :
    TInvariant := by
  intro E _ _ k r z z' i D f Y p q hz hz' hDom hf s hs s' hs' g hg
  have hDo : IsOpen D := hDom.1
  obtain ⟨hVl, hVr⟩ := hV k r z z' i hz hz'
  have hsG : s ∈ Glev k r i := ((hS k r z i hz).2 s hs).1
  have hs'G : s' ∈ Glev k r i := ((hS k r z' i hz').2 s' hs').1
  have h1z : (1 : Mx k r) ∈ Slev k r z i := (hS k r z i hz).1
  have h1z' : (1 : Mx k r) ∈ Slev k r z' i := (hS k r z' i hz').1
  have hh : s * g ∈ Glev k r i ∩ D := by
    refine ⟨hGr k r i s hsG g hg.1, ?_⟩
    simpa using hDom.2 g hg s hs 1 h1z'
  have hR : ∀ y ∈ Glev k r i ∩ D, y * s' ∈ Glev k r i ∩ D := fun y hy =>
    ⟨hGr k r i y hy.1 s' hs'G, by simpa using hDom.2 y hy 1 h1z s' hs'⟩
  rw [left_step hL k r z z' i Y p q (fun y => f (y * s')) s g (hVl s hs g).1 (hVl s hs g).2]
  obtain ⟨hQP, hPQ, hxv, hxbv, hyv⟩ := hVr s' hs'
  have hf' : SmoothLev k r i D (ext k r i D (fun p : Pt k r i D => f p.1)) :=
    lev_congr hDo (fun y hy => (ext_at (φ := fun p : Pt k r i D => f p.1) hy).symm) hf
  let x0 : Sm E k r i D := ⟨fun p => f p.1, hf'⟩
  have hrep : Rep f x0.1 := fun _ _ => rfl
  have hrep' : Rep (fun x => f (x * s')) (RL (E := E) hP hC hDo hR hRS hs'G x0).1 := fun _ _ => rfl
  have hint : ∀ a b, Ealg (E := E) (i := i) hP hC hDo a b * RL (E := E) hP hC hDo hR hRS hs'G =
      RL (E := E) hP hC hDo hR hRS hs'G * Econj (Ealg (E := E) (i := i) hP hC hDo) (blk i s'⁻¹) (blk i s') a b :=
    fun a b => RL_inter hP hC hDo hR hRS hs'G hRt a b
  have hGl : GlRel (Ealg (E := E) (i := i) hP hC hDo) := Ealg_gl hP hC hDo hG
  have cov := hCC (Module.End ℂ (Sm E k r i D)) (mdim k r i) (Ealg (E := E) (i := i) hP hC hDo)
    (blk i s'⁻¹) (blk i s') hGl hQP hPQ
  obtain ⟨hyvy, hybvy⟩ := hyv (s * g) hh.1
  have hy' := hR (s * g) hh
  match p, q with
  | 0, 0 =>
    rw [tl00, tl00, qdet_rep hP hC hDo _ hrep' (s * g) hh, qdet_rep hP hC hDo _ hrep (s * g * s') hy',
      RL_apply hP hC hDo hR hRS hs'G _ _ (qdet_inter _ _ _ hint _) x0 (s * g) hh,
      (cov (uC k r i Y) 0 0 0 0).1]
  | 0, 1 =>
    have e := (cov (uC k r i Y - 1) (xv k r z' i) 0 (ybv k r z i (s * g * s')) 0).2.1
    rw [hxv, ← hybvy] at e
    rw [tl01, tl01, Pi.neg_apply, Pi.neg_apply, chat_rep hP hC hDo _ _ _ hrep' (s * g) hh,
      chat_rep hP hC hDo _ _ _ hrep (s * g * s') hy',
      RL_apply hP hC hDo hR hRS hs'G _ _ (chatA_inter _ _ _ hint _ _ _) x0 (s * g) hh, e]
  | 1, 0 =>
    have e := (cov (uC k r i Y) (yv k r z i (s * g * s')) 0 (xbv k r z' i) 0).2.1
    rw [← hyvy, hxbv] at e
    rw [tl10, tl10, Pi.neg_apply, Pi.neg_apply, chat_rep hP hC hDo _ _ _ hrep' (s * g) hh,
      chat_rep hP hC hDo _ _ _ hrep (s * g * s') hy',
      RL_apply hP hC hDo hR hRS hs'G _ _ (chatA_inter _ _ _ hint _ _ _) x0 (s * g) hh, e]
  | 1, 1 =>
    have e := (cov (uC k r i Y - 1) (yv k r z i (s * g * s')) (xv k r z' i) (ybv k r z i (s * g * s'))
      (xbv k r z' i)).2.2
    rw [← hyvy, hxv, ← hybvy, hxbv] at e
    rw [tl11, tl11, Pi.neg_apply, Pi.neg_apply, second_capelli_minor_represents hP hC hDo _ _ _ _ _ hrep' (s * g) hh,
      second_capelli_minor_represents hP hC hDo _ _ _ _ _ hrep (s * g * s') hy',
      RL_apply hP hC hDo hR hRS hs'G _ _ (second_capelli_minor_intertwines _ _ _ hint _ _ _ _ _) x0 (s * g) hh, e]

end Formalism.FourierDecayAlt.Q.TInvW
end
end

section
open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.Q.TInvW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma glev_mul' {i : Fin (r + 1)} {g h : Mx k r} (hg : g ∈ Glev k r i) (hh : h ∈ Glev k r i) :
    g * h ∈ Glev k r i := by
  simp only [Glev, UH, Set.mem_setOf_eq] at hg hh ⊢
  obtain ⟨hgU, hgF⟩ := hg
  obtain ⟨hhU, hhF⟩ := hh
  refine ⟨?_, fun a ha => ⟨?_, ?_⟩⟩
  · rw [conjTranspose_mul, show hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h by
      simp only [mul_assoc], hgU, hhU]
  · rw [← Matrix.mulVec_mulVec, (hhF a ha).1, (hgF a ha).1]
  · rw [← Matrix.mulVec_mulVec, (hhF a ha).2, (hgF a ha).2]

theorem transfer_invariance_group_mul : StepGrp := fun _ _ _ _ hg _ hh => glev_mul' hg hh

lemma glev_unit {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) : g * g⁻¹ = 1 ∧ g⁻¹ * g = 1 := by
  have hU : gᴴ * Hpk k r * g = Hpk k r := by
    simp only [Glev, UH, Set.mem_setOf_eq] at hg
    exact hg.1
  have hl : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [show Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) by simp only [mul_assoc], hU, hpk_sq]
  rw [Matrix.inv_eq_left_inv hl]
  exact ⟨mul_eq_one_comm.mp hl, hl⟩

lemma inv_fix {g : Mx k r} (hu : g⁻¹ * g = 1) {v : Fin (2 * r + k + 1) → ℂ} (h : g *ᵥ v = v) :
    g⁻¹ *ᵥ v = v := by
  conv_lhs => rw [← h]
  rw [Matrix.mulVec_mulVec, hu, Matrix.one_mulVec]

lemma glev_inv {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) : g⁻¹ ∈ Glev k r i := by
  have hu := glev_unit hg
  simp only [Glev, UH, Set.mem_setOf_eq] at hg ⊢
  obtain ⟨hU, hF⟩ := hg
  refine ⟨?_, fun a ha => ⟨inv_fix hu.2 (hF a ha).1, inv_fix hu.2 (hF a ha).2⟩⟩
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hU]
    _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by rw [conjTranspose_mul]; simp only [mul_assoc]
    _ = Hpk k r := by rw [hu.1, conjTranspose_one, one_mul, mul_one]

lemma H_esI (a : Fin r) (w : Fin (2 * r + k + 1) → ℂ) : (Hpk k r *ᵥ w) (esI k r a) = w (eI k r a) := by
  have ha := a.isLt
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (eI k r a)]
  · have h1 : Hpk k r (esI k r a) (eI k r a) = 1 := by
      simp only [Hpk, eI, esI, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [h1, one_mul]
  · intro j _ hj
    have hj' : j.val ≠ a.val := fun h => hj (Fin.ext h)
    have hjl := j.isLt
    have h0 : Hpk k r (esI k r a) j = 0 := by
      simp only [Hpk, esI, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma H_eI (a : Fin r) (w : Fin (2 * r + k + 1) → ℂ) : (Hpk k r *ᵥ w) (eI k r a) = w (esI k r a) := by
  have ha := a.isLt
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (esI k r a)]
  · have h1 : Hpk k r (eI k r a) (esI k r a) = 1 := by
      simp only [Hpk, eI, esI, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [h1, one_mul]
  · intro j _ hj
    have hj' : j.val ≠ 2 * r + k - a.val := fun h => hj (Fin.ext h)
    have hjl := j.isLt
    have h0 : Hpk k r (eI k r a) j = 0 := by
      simp only [Hpk, eI, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma coord {g : Mx k r} (hg : g ∈ UH (Hpk k r)) (c d : Fin (2 * r + k + 1))
    (hcd : ∀ w, (Hpk k r *ᵥ w) c = w d) (hfix : g *ᵥ bvec c = bvec c) (v : Fin (2 * r + k + 1) → ℂ) :
    (g *ᵥ v) d = v d := by
  have hU : gᴴ * Hpk k r * g = Hpk k r := hg
  have hcol : ∀ l, g l c = bvec c l := fun l => by
    rw [← congrFun hfix l]
    simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]
  have hrow : ∀ j, (Hpk k r * g) c j = Hpk k r c j := by
    intro j
    have h1 := congrFun (congrFun hU c) j
    rw [Matrix.mul_assoc, Matrix.mul_apply] at h1
    rw [← h1, Finset.sum_eq_single c]
    · rw [conjTranspose_apply, hcol]
      simp [bvec]
    · intro l _ hl
      rw [conjTranspose_apply, hcol]
      simp [bvec, Pi.single_apply, hl]
    · intro h
      exact absurd (Finset.mem_univ c) h
  have key : (Hpk k r *ᵥ (g *ᵥ v)) c = (Hpk k r *ᵥ v) c := by
    rw [Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct, hrow]
  calc (g *ᵥ v) d = (Hpk k r *ᵥ (g *ᵥ v)) c := (hcd _).symm
    _ = (Hpk k r *ᵥ v) c := key
    _ = v d := hcd v

lemma outer {i : Fin (r + 1)} (q : Fin (2 * r + k + 1)) (hq : ∀ c, q ≠ posL k r i c) :
    ∃ a : Fin r, a.val < i.val ∧ (q = eI k r a ∨ q = esI k r a) := by
  have hq' := q.isLt
  have hi := i.isLt
  by_cases h1 : q.val < i.val
  · exact ⟨⟨q.val, by omega⟩, h1, Or.inl (Fin.ext rfl)⟩
  · have h2 : 2 * r + k - i.val < q.val := by
      by_contra h3
      exact hq ⟨q.val - i.val, by unfold mdim; omega⟩ (Fin.ext (by simp only [posL]; omega))
    exact ⟨⟨2 * r + k - q.val, by omega⟩, by simp only; omega, Or.inr (Fin.ext (by simp only [esI]; omega))⟩

lemma glev_fix_outer {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) (q : Fin (2 * r + k + 1))
    (hq : ∀ c, q ≠ posL k r i c) : g *ᵥ bvec q = bvec q := by
  obtain ⟨a, ha, hq'⟩ := outer q hq
  have hg' : g ∈ UH (Hpk k r) ∧ ∀ a : Fin r, a.val < i.val →
      g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a) := hg
  rcases hq' with rfl | rfl
  · exact (hg'.2 a ha).1
  · exact (hg'.2 a ha).2

lemma glev_col {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) (p q : Fin (2 * r + k + 1))
    (hq : ∀ c, q ≠ posL k r i c) : g p q = bvec q p := by
  rw [← congrFun (glev_fix_outer hg q hq) p]
  simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]

lemma glev_row {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) (q : Fin (2 * r + k + 1))
    (hq : ∀ c, q ≠ posL k r i c) (v : Fin (2 * r + k + 1) → ℂ) : (g *ᵥ v) q = v q := by
  have hg' : g ∈ UH (Hpk k r) ∧ ∀ a : Fin r, a.val < i.val →
      g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a) := hg
  obtain ⟨a, ha, hq'⟩ := outer q hq
  rcases hq' with rfl | rfl
  · exact coord hg'.1 (esI k r a) (eI k r a) (H_esI a) (hg'.2 a ha).2 v
  · exact coord hg'.1 (eI k r a) (esI k r a) (H_eI a) (hg'.2 a ha).1 v

lemma glev_row' {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) (q p : Fin (2 * r + k + 1))
    (hq : ∀ c, q ≠ posL k r i c) : g q p = bvec p q := by
  rw [← glev_row hg q hq (bvec p)]
  simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]

lemma sum_posL {M : Type*} [AddCommMonoid M] {i : Fin (r + 1)} (F : Fin (2 * r + k + 1) → M)
    (hF : ∀ q, (∀ c, q ≠ posL k r i c) → F q = 0) :
    ∑ q, F q = ∑ c : Fin (mdim k r i), F (posL k r i c) := (Fintype.sum_of_injective (posL k r i) (fun _ _ h => posL_inj h) _ F
    (fun q hq => hF q (fun c hc => hq ⟨c, hc.symm⟩)) (fun _ => rfl)).symm

lemma bvec_posL_outer {i : Fin (r + 1)} (a : Fin (mdim k r i)) (q : Fin (2 * r + k + 1))
    (hq : ∀ c, q ≠ posL k r i c) : bvec q (posL k r i a) = 0 ∧ bvec (posL k r i a) q = 0 := ⟨by simp [bvec, Pi.single_apply, hq a, (hq a).symm], by simp [bvec, Pi.single_apply, hq a, (hq a).symm]⟩

lemma n_fix {z : Fin (2 * r + k + 1) → ℂ} {i : Fin (r + 1)} (hz : inWb k r z) {m : Mx k r}
    (hm : m ∈ Nlev k r i) : m *ᵥ fvec k r z i = fvec k r z i := by
  unfold Nlev at hm
  simp only [QuantumDeterminants.Nset, Set.mem_inter_iff, Set.mem_setOf_eq] at hm
  obtain ⟨⟨_, hcol, hmid⟩, hG⟩ := hm
  unfold inWb at hz
  unfold fvec
  split_ifs with hi
  · funext x
    rw [show (m *ᵥ bvec (eI k r ⟨i.val, hi⟩)) x = m x (eI k r ⟨i.val, hi⟩) by
      simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]]
    by_cases hx : i.val ≤ x.val
    · rw [hcol ⟨i.val, hi⟩ x hx]
      simp [bvec, Pi.single_apply]
    · have hout : ∀ c, x ≠ posL k r i c := fun c h => hx (by
        have h2 := congrArg Fin.val h
        simp only [posL] at h2
        omega)
      rw [glev_row' hG x (eI k r ⟨i.val, hi⟩) hout]
  · funext x
    by_cases hx : r ≤ x.val
    · simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single x]
      · by_cases hxk : x.val ≤ r + k
        · rw [hmid x x hx hxk hx]
          simp
        · rw [hz x (Or.inr (by omega)), mul_zero]
      · intro j _ hj
        by_cases hjm : r ≤ j.val ∧ j.val ≤ r + k
        · rw [hmid x j hjm.1 hjm.2 hx, if_neg (Ne.symm hj), zero_mul]
        · rw [hz j (by omega), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · have hout : ∀ c, x ≠ posL k r i c := fun c h => hx (by
        have h2 := congrArg Fin.val h
        simp only [posL] at h2
        omega)
      exact glev_row hG x hout z

lemma h_fix {z : Fin (2 * r + k + 1) → ℂ} {i : Fin (r + 1)} {h : Mx k r} (hh : h ∈ UWset k r z) :
    h *ᵥ fvec k r z i = fvec k r z i := by
  simp only [UWset, Set.mem_setOf_eq] at hh
  unfold fvec
  split_ifs with hi
  · exact (hh.2.1 _).1
  · exact hh.2.2

theorem transfer_invariance_smooth : StepS := by
  intro k r z i hz
  have hUW : ∀ h ∈ UWset k r z, h ∈ Glev k r i := by
    intro h hh
    simp only [UWset, Glev, Set.mem_setOf_eq] at hh ⊢
    exact ⟨hh.1, fun a _ => hh.2.1 a⟩
  simp only [Slev, Set.mem_setOf_eq]
  refine ⟨⟨1, ?_, 1, ?_, (mul_one 1).symm⟩, ?_⟩
  · simp [UWset, UH]
  · simp [Nlev, QuantumDeterminants.Nset, Glev, UH, Matrix.one_apply]
  · rintro s ⟨h, hh, m, hm, rfl⟩
    have hmG : m ∈ Glev k r i := by
      unfold Nlev at hm
      exact hm.2
    refine ⟨glev_mul' (hUW h hh) hmG, ?_⟩
    rw [← Matrix.mulVec_mulVec, n_fix hz hm, h_fix hh]

lemma herm_uh {s : Mx k r} (hs : s ∈ UH (Hpk k r)) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (s *ᵥ v) (s *ᵥ w) = herm (Hpk k r) v w := by
  have hs' : sᴴ * Hpk k r * s = Hpk k r := hs
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  simp only [← Matrix.mul_assoc, hs']

lemma herm_col (M : Mx k r) (q : Fin (2 * r + k + 1)) (w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (M *ᵥ bvec q) w = (star w ᵥ* Hpk k r ᵥ* M) q := by
  unfold herm
  rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_vecMul]
  simp [bvec]

lemma herm_bv (q : Fin (2 * r + k + 1)) (w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (bvec q) w = (star w ᵥ* Hpk k r) q := by
  unfold herm
  rw [Matrix.dotProduct_mulVec]
  simp [bvec]

lemma uh_H_inv {s : Mx k r} (hs : s ∈ UH (Hpk k r)) (hu : s * s⁻¹ = 1) :
    Hpk k r * s⁻¹ = sᴴ * Hpk k r := by
  have hs' : sᴴ * Hpk k r * s = Hpk k r := hs
  calc Hpk k r * s⁻¹ = sᴴ * Hpk k r * s * s⁻¹ := by rw [hs']
    _ = sᴴ * Hpk k r := by rw [mul_assoc (sᴴ * Hpk k r), hu, mul_one]

theorem transfer_invariance_vector : StepVec := by
  intro k r z z' i hz hz'
  have bo : ∀ (a : Fin (mdim k r i)) q, (∀ c, q ≠ posL k r i c) →
      bvec q (posL k r i a) = 0 ∧ bvec (posL k r i a) q = 0 :=
    fun a q hq => bvec_posL_outer a q hq
  have blk_mul : ∀ s t : Mx k r, s ∈ Glev k r i → blk i (s * t) = blk i s * blk i t := by
    intro s t hs
    ext a b
    simp only [blk, Matrix.mul_apply]
    exact sum_posL (fun q => s (posL k r i a) q * t q (posL k r i b)) (fun q hq => by
      show s (posL k r i a) q * t q (posL k r i b) = 0
      rw [glev_col hs (posL k r i a) q hq, (bo a q hq).1, zero_mul])
  have blk_one : blk i (1 : Mx k r) = 1 := by
    ext a b
    simp only [blk, Matrix.one_apply]
    by_cases h : a = b
    · simp [h]
    · rw [if_neg (fun e => h (posL_inj e)), if_neg h]
  have mv_blk : ∀ s ∈ Glev k r i, ∀ v : Fin (2 * r + k + 1) → ℂ,
      (blk i s *ᵥ fun j => v (posL k r i j)) = fun j => (s *ᵥ v) (posL k r i j) := by
    intro s hs v
    funext a
    simp only [blk, Matrix.mulVec, dotProduct]
    exact (sum_posL (fun q => s (posL k r i a) q * v q) (fun q hq => by
      show s (posL k r i a) q * v q = 0
      rw [glev_col hs (posL k r i a) q hq, (bo a q hq).1, zero_mul])).symm
  have vm_blk : ∀ t ∈ Glev k r i, ∀ x : Fin (2 * r + k + 1) → ℂ,
      ((fun j => x (posL k r i j)) ᵥ* blk i t) = fun j => (x ᵥ* t) (posL k r i j) := by
    intro t ht x
    funext b
    simp only [blk, Matrix.vecMul, dotProduct]
    exact (sum_posL (fun q => x q * t q (posL k r i b)) (fun q hq => by
      show x q * t q (posL k r i b) = 0
      rw [glev_row' ht q (posL k r i b) hq, (bo b q hq).2, mul_zero])).symm
  have hS := transfer_invariance_smooth k r z i hz
  have hS' := transfer_invariance_smooth k r z' i hz'
  refine ⟨fun s hs g => ?_, fun s' hs' => ?_⟩
  · obtain ⟨hsG, hsf⟩ := hS.2 s hs
    have hu := glev_unit hsG
    have hsU : s ∈ UH (Hpk k r) := by
      simp only [Glev, Set.mem_setOf_eq] at hsG
      exact hsG.1
    have hinv : s⁻¹ *ᵥ fvec k r z i = fvec k r z i := inv_fix hu.2 hsf
    constructor
    · funext j
      simp only [yv]
      rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, hinv]
    · funext j
      simp only [ybv]
      conv_lhs => rw [← hsf]
      rw [← Matrix.mulVec_mulVec, herm_uh hsU]
  · obtain ⟨hsG, hsf⟩ := hS'.2 s' hs'
    have hu := glev_unit hsG
    have hiG := glev_inv hsG
    have hsU : s' ∈ UH (Hpk k r) := by
      have h0 := hsG
      simp only [Glev, Set.mem_setOf_eq] at h0
      exact h0.1
    refine ⟨?_, ?_, ?_, ?_, fun g hg => ⟨?_, ?_⟩⟩
    · rw [← blk_mul _ _ hsG, hu.1, blk_one]
    · rw [← blk_mul _ _ hiG, hu.2, blk_one]
    · unfold xv
      rw [mv_blk _ hsG, hsf]
    · unfold xbv
      simp only [herm_bv]
      rw [vm_blk _ hiG, Matrix.vecMul_vecMul, uh_H_inv hsU hu.1, ← Matrix.vecMul_vecMul, ← Matrix.star_mulVec, hsf]
    · unfold yv
      rw [mv_blk _ hsG]
      funext j
      rw [Matrix.mulVec_mulVec, Matrix.mul_inv_rev, ← Matrix.mul_assoc, hu.1, Matrix.one_mul]
    · unfold ybv
      simp only [herm_col]
      rw [vm_blk _ hiG]
      simp only [Matrix.vecMul_vecMul, Matrix.mul_assoc, hu.1, Matrix.mul_one]

theorem transfer_invariance_restriction : StepRSm := by
  intro E _ _ k r i D f s' hs' hD hf g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf (g₀ * s') ⟨glev_mul' hg₀.1 hs', hD g₀ hg₀⟩
  let L : Mx k r →L[ℝ] Mx k r := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ s')
  have hL : ∀ x, L x = x * s' := fun _ => rfl
  refine ⟨L ⁻¹' U, fun x => F (L x), hU.preimage L.continuous, by simpa [hL] using hgU,
    hF.comp L.contDiff.contDiffOn (fun _ hx => hx), fun x hx hxG => ?_⟩
  have hx' : x * s' ∈ U := by rw [← hL]; exact hx
  show f (x * s') = F (L x)
  rw [hL]
  exact hfF _ hx' (glev_mul' hxG hs')

end Formalism.FourierDecayAlt.Q.TInvW
end
end

section
open Matrix Finset Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.Q.TInvW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma hpk_inv : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_right_inv (Hpk_sq k r)

lemma hpk_unit : IsUnit (Hpk k r) := ⟨⟨Hpk k r, Hpk k r, Hpk_sq k r, Hpk_sq k r⟩, rfl⟩

lemma hpk_hh (A : Mx k r) : Hpk k r * (Hpk k r * A) = A := by rw [← mul_assoc, Hpk_sq, one_mul]

lemma hpart1_skew (Z : Mx k r) :
    (hpart1 (Hpk k r) Z)ᴴ = -(Hpk k r * hpart1 (Hpk k r) Z * Hpk k r) := by
  unfold hpart1
  rw [hpk_inv]
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp
  simp only [conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, Hpk_herm, hs,
    mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_assoc, hpk_hh, Hpk_sq, mul_one]
  rw [← smul_neg, neg_sub]

lemma hpart2_skew (Z : Mx k r) :
    (hpart2 (Hpk k r) Z)ᴴ = -(Hpk k r * hpart2 (Hpk k r) Z * Hpk k r) := by
  unfold hpart2
  rw [hpk_inv]
  have hs : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by simp
  simp only [conjTranspose_smul, conjTranspose_add, conjTranspose_mul, conjTranspose_conjTranspose, Hpk_herm, hs,
    mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_assoc, hpk_hh, Hpk_sq, mul_one]
  rw [neg_smul, add_comm Zᴴ]

lemma skew_real (X : Mx k r) (hX : Xᴴ = -(Hpk k r * X * Hpk k r)) (t : ℝ) :
    ((t : ℂ) • X)ᴴ = -(Hpk k r * ((t : ℂ) • X) * Hpk k r) := by
  rw [conjTranspose_smul, hX]
  simp [Complex.star_def, Complex.conj_ofReal, mul_smul_comm, smul_mul_assoc]

lemma exp_mem_UH (Y : Mx k r) (hY : Yᴴ = -(Hpk k r * Y * Hpk k r)) :
    NormedSpace.exp Y ∈ UH (Hpk k r) := by
  show (NormedSpace.exp Y)ᴴ * Hpk k r * NormedSpace.exp Y = Hpk k r
  have e1 : Yᴴ = Hpk k r * (-Y) * (Hpk k r)⁻¹ := by
    rw [hY, hpk_inv, mul_neg, neg_mul]
  rw [← Matrix.exp_conjTranspose, e1, Matrix.exp_conj _ _ hpk_unit, hpk_inv]
  simp only [mul_assoc, hpk_hh]
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl Y).neg_left, neg_add_cancel, NormedSpace.exp_zero, mul_one]

lemma exp_fix (Y : Mx k r) (c : Fin (2 * r + k + 1)) (hY : ∀ x, Y x c = 0) :
    NormedSpace.exp Y *ᵥ bvec c = bvec c := by
  set P : Mx k r := Matrix.single c c 1 with hPdef
  have hYP : Y * P = 0 := by
    ext x y
    simp only [hPdef, Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    split_ifs with h
    · rw [← h.1, hY, mul_one]
    · exact mul_zero _
  have hne : NormedSpace.exp Y ≠ 0 := by
    intro h0
    have hc : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
      rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
        NormedSpace.exp_zero]
    rw [h0, Matrix.mul_zero] at hc
    have := congrFun (congrFun hc ⟨0, by omega⟩) ⟨0, by omega⟩
    simp at this
  have hsum : Summable (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • Y ^ n) := by
    by_contra hns
    apply hne
    rw [congrFun (NormedSpace.exp_eq_tsum ℂ) Y]
    exact tsum_eq_zero_of_not_summable hns
  have hhas : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • Y ^ n) (NormedSpace.exp Y) := by
    have := hsum.hasSum
    rwa [← congrFun (NormedSpace.exp_eq_tsum ℂ) Y] at this
  have h1 := hhas.mul_right P
  have h2 : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • Y ^ n * P) P := by
    have := hasSum_single (f := fun n : ℕ => ((n.factorial : ℂ)⁻¹) • Y ^ n * P) 0 (by
      intro m hm
      obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
      rw [Matrix.smul_mul, pow_succ, Matrix.mul_assoc, hYP, Matrix.mul_zero, smul_zero])
    simpa using this
  have hEP : NormedSpace.exp Y * P = P := h1.unique h2
  have hPv : P *ᵥ bvec c = bvec c := by
    ext x
    by_cases h : x = c
    · subst h; simp [hPdef, bvec, Matrix.mulVec, dotProduct, Matrix.single_apply, Pi.single_apply]
    · simp [hPdef, bvec, Matrix.mulVec, dotProduct, Matrix.single_apply, Pi.single_apply, h, Ne.symm h]
  rw [← hPv, Matrix.mulVec_mulVec, hEP]

lemma exp_mem_glev (i : Fin (r + 1)) (X : Mx k r) (hX : Xᴴ = -(Hpk k r * X * Hpk k r))
    (hc : ∀ a : Fin r, a.val < i.val → ∀ x, X x (eI k r a) = 0 ∧ X x (esI k r a) = 0) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i := by
  simp only [Glev, Set.mem_setOf_eq]
  refine ⟨exp_mem_UH _ (skew_real X hX t), fun a ha => ⟨exp_fix _ _ fun x => ?_, exp_fix _ _ fun x => ?_⟩⟩
  · rw [Matrix.smul_apply, (hc a ha x).1, smul_zero]
  · rw [Matrix.smul_apply, (hc a ha x).2, smul_zero]

lemma hpk_zero (i : Fin (r + 1)) (p : Fin (mdim k r i)) (a : Fin r) (ha : a.val < i.val) :
    Hpk k r (posL k r i p) (eI k r a) = 0 ∧ Hpk k r (posL k r i p) (esI k r a) = 0 := by
  have hp := p.isLt
  have ha' := a.isLt
  have hi := i.isLt
  unfold mdim at hp
  simp only [Hpk, posL, eI, esI, Fin.mk.injEq]
  constructor <;> split_ifs <;> first | rfl | (exfalso; omega)

lemma unit_col (i : Fin (r + 1)) (p q : Fin (mdim k r i)) (c : Fin (2 * r + k + 1))
    (hcq : c ≠ posL k r i q) (hHc : Hpk k r (posL k r i p) c = 0) (x : Fin (2 * r + k + 1)) :
    (Matrix.single (posL k r i p) (posL k r i q) (1 : ℂ)) x c = 0 ∧
    (Hpk k r * (Matrix.single (posL k r i p) (posL k r i q) (1 : ℂ))ᴴ * Hpk k r) x c = 0 := by
  constructor
  · simp [Matrix.single_apply, hcq, Ne.symm hcq]
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l = posL k r i p
    · rw [hl, hHc, mul_zero]
    · have h0 : (Hpk k r * (Matrix.single (posL k r i p) (posL k r i q) (1 : ℂ))ᴴ) x l = 0 := by
        rw [Matrix.mul_apply]
        refine Finset.sum_eq_zero fun m _ => ?_
        simp [Matrix.conjTranspose_apply, Matrix.single_apply, hl, Ne.symm hl]
      rw [h0, zero_mul]

lemma posL_ne (i : Fin (r + 1)) (q : Fin (mdim k r i)) (a : Fin r) (ha : a.val < i.val) :
    eI k r a ≠ posL k r i q ∧ esI k r a ≠ posL k r i q := by
  have hq := q.isLt
  have ha' := a.isLt
  unfold mdim at hq
  refine ⟨fun h => ?_, fun h => ?_⟩ <;>
  · have h2 := congrArg Fin.val h
    simp only [eI, esI, posL] at h2
    omega

lemma hpart_cols (i : Fin (r + 1)) (p q : Fin (mdim k r i)) :
    (∀ a : Fin r, a.val < i.val → ∀ x,
      hpart1 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1) x (eI k r a) = 0 ∧
      hpart1 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1) x (esI k r a) = 0) ∧
    (∀ a : Fin r, a.val < i.val → ∀ x,
      hpart2 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1) x (eI k r a) = 0 ∧
      hpart2 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1) x (esI k r a) = 0) := by
  have key : ∀ a : Fin r, a.val < i.val → ∀ x c, (c = eI k r a ∨ c = esI k r a) →
      (Matrix.single (posL k r i p) (posL k r i q) (1 : ℂ)) x c = 0 ∧
      (Hpk k r * (Matrix.single (posL k r i p) (posL k r i q) (1 : ℂ))ᴴ * Hpk k r) x c = 0 := by
    intro a ha x c hc
    obtain ⟨n1, n2⟩ := posL_ne i q a ha
    obtain ⟨z1, z2⟩ := hpk_zero i p a ha
    rcases hc with rfl | rfl
    · exact unit_col i p q _ n1 z1 x
    · exact unit_col i p q _ n2 z2 x
  refine ⟨fun a ha x => ?_, fun a ha x => ?_⟩ <;>
  · obtain ⟨e1, e2⟩ := key a ha x _ (Or.inl rfl)
    obtain ⟨e3, e4⟩ := key a ha x _ (Or.inr rfl)
    simp only [hpart1, hpart2]
    rw [hpk_inv]
    refine ⟨?_, ?_⟩ <;>
    · first
      | rw [Matrix.smul_apply, Matrix.sub_apply]
      | rw [Matrix.smul_apply, Matrix.add_apply]
      simp only [e1, e2, e3, e4, sub_zero, add_zero, smul_zero]

theorem exp_hpart1_mem (i : Fin (r + 1)) (p q : Fin (mdim k r i)) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • hpart1 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1))
      ∈ Glev k r i := exp_mem_glev i _ (hpart1_skew _) (hpart_cols i p q).1 t

theorem exp_hpart2_mem (i : Fin (r + 1)) (p q : Fin (mdim k r i)) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • hpart2 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1))
      ∈ Glev k r i := exp_mem_glev i _ (hpart2_skew _) (hpart_cols i p q).2 t

theorem rdV_ext {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (i : Fin (r + 1)) (X : Mx k r) (hX : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i)
    (f F : Mx k r → E) (U : Set (Mx k r)) (g : Mx k r) (hU : IsOpen U) (hg : g ∈ U)
    (hgG : g ∈ Glev k r i) (hF : ContDiffOn ℝ ∞ F U)
    (hfF : ∀ x ∈ U, x ∈ Glev k r i → f x = F x) :
    RdV X f g = fderiv ℝ F g (g * X) := by
  have hγ := hasDerivAt_mul_exp_smul_zero g X
  have hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by
    simp [NormedSpace.exp_zero]
  have hFd : DifferentiableAt ℝ F g :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)
  have hcomp : HasDerivAt (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X)))
      (fderiv ℝ F g (g * X)) 0 :=
    hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  have hev : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0]
      (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) := by
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
      hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hg)
    filter_upwards [hmem] with t ht
    exact hfF _ ht (glev_mul' hgG (hX t))
  exact (hcomp.congr_of_eventuallyEq hev).deriv

theorem transfer_invariance_congruence : StepCongr := by
  intro E _ _ k r i D a b f f' g hD hg hff
  have key : ∀ X : Mx k r, (∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i) →
      RdV X f g = RdV X f' g := by
    intro X hX
    unfold RdV
    apply Filter.EventuallyEq.deriv_eq
    have hγ := hasDerivAt_mul_exp_smul_zero g X
    have hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by simp [NormedSpace.exp_zero]
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ D :=
      hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hD.mem_nhds hg.2)
    filter_upwards [hmem] with t ht
    exact hff _ ⟨glev_mul' hg.1 (hX t), ht⟩
  show RdV _ f g + Complex.I • RdV _ f g = RdV _ f' g + Complex.I • RdV _ f' g
  rw [key _ (exp_hpart1_mem i a b), key _ (exp_hpart2_mem i a b)]

lemma rdV_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (X s' g : Mx k r) (f : Mx k r → E)
    (hu1 : s' * s'⁻¹ = 1) (hu2 : s'⁻¹ * s' = 1) :
    RdV X (fun x => f (x * s')) g = RdV (s'⁻¹ * X * s') f (g * s') := by
  have hU : IsUnit s' := ⟨⟨s', s'⁻¹, hu1, hu2⟩, rfl⟩
  simp only [RdV]
  congr 1
  funext t
  congr 1
  rw [show ((t : ℂ) • (s'⁻¹ * X * s')) = s'⁻¹ * ((t : ℂ) • X) * s' by rw [mul_smul_comm, smul_mul_assoc],
    Matrix.exp_conj' _ _ hU]
  simp only [mul_assoc]
  rw [← mul_assoc s' s'⁻¹, hu1, one_mul]

lemma uh_inv_eq {s : Mx k r} (hs : s ∈ UH (Hpk k r)) : s⁻¹ = Hpk k r * sᴴ * Hpk k r := by
  have hs' : sᴴ * Hpk k r * s = Hpk k r := hs
  refine Matrix.inv_eq_left_inv ?_
  rw [show Hpk k r * sᴴ * Hpk k r * s = Hpk k r * (sᴴ * Hpk k r * s) by simp only [mul_assoc], hs', Hpk_sq]

lemma conj_part {s : Mx k r} (hs : s ∈ UH (Hpk k r)) (Z : Mx k r) :
    (Hpk k r)⁻¹ * (s⁻¹ * Z * s)ᴴ * Hpk k r = s⁻¹ * ((Hpk k r)⁻¹ * Zᴴ * Hpk k r) * s := by
  have hi := uh_inv_eq hs
  have h1 : sᴴ = Hpk k r * s⁻¹ * Hpk k r := by
    rw [hi]
    simp only [mul_assoc, hpk_hh, Hpk_sq, mul_one]
  have h2 : (s⁻¹)ᴴ = Hpk k r * s * Hpk k r := by
    rw [hi, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, Hpk_herm]
    simp only [mul_assoc]
  rw [hpk_inv, conjTranspose_mul, conjTranspose_mul, h2, h1]
  simp only [mul_assoc, hpk_hh, Hpk_sq, mul_one]

lemma hpart1_conj {s : Mx k r} (hs : s ∈ UH (Hpk k r)) (Z : Mx k r) :
    hpart1 (Hpk k r) (s⁻¹ * Z * s) = s⁻¹ * hpart1 (Hpk k r) Z * s := by
  unfold hpart1
  rw [conj_part hs Z]
  simp only [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_assoc]

lemma hpart2_conj {s : Mx k r} (hs : s ∈ UH (Hpk k r)) (Z : Mx k r) :
    hpart2 (Hpk k r) (s⁻¹ * Z * s) = s⁻¹ * hpart2 (Hpk k r) Z * s := by
  unfold hpart2
  rw [conj_part hs Z]
  simp only [mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_assoc]

lemma exp_conj_mem {i : Fin (r + 1)} {s : Mx k r} (hs : s ∈ Glev k r i) {X : Mx k r}
    (hX : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • (s⁻¹ * X * s)) ∈ Glev k r i := by
  have hu := glev_unit hs
  have hU : IsUnit s := ⟨⟨s, s⁻¹, hu.1, hu.2⟩, rfl⟩
  rw [show ((t : ℂ) • (s⁻¹ * X * s)) = s⁻¹ * ((t : ℂ) • X) * s by rw [mul_smul_comm, smul_mul_assoc],
    Matrix.exp_conj' _ _ hU]
  exact glev_mul' (glev_mul' (glev_inv hs) (hX t)) hs

lemma hpart1_add (Z W : Mx k r) :
    hpart1 (Hpk k r) (Z + W) = hpart1 (Hpk k r) Z + hpart1 (Hpk k r) W := by
  unfold hpart1
  rw [conjTranspose_add, mul_add, add_mul, ← smul_add]
  congr 1
  abel

lemma hpart2_add (Z W : Mx k r) :
    hpart2 (Hpk k r) (Z + W) = hpart2 (Hpk k r) Z + hpart2 (Hpk k r) W := by
  unfold hpart2
  rw [conjTranspose_add, mul_add, add_mul, ← smul_add]
  congr 1
  abel

lemma hpart1_real (a : ℝ) (Z : Mx k r) :
    hpart1 (Hpk k r) ((a : ℂ) • Z) = (a : ℂ) • hpart1 (Hpk k r) Z := by
  unfold hpart1
  have hst : star (a : ℂ) = a := Complex.conj_ofReal a
  rw [conjTranspose_smul, hst, mul_smul_comm, smul_mul_assoc, ← smul_sub, smul_comm]

lemma hpart2_real (a : ℝ) (Z : Mx k r) :
    hpart2 (Hpk k r) ((a : ℂ) • Z) = (a : ℂ) • hpart2 (Hpk k r) Z := by
  unfold hpart2
  have hst : star (a : ℂ) = a := Complex.conj_ofReal a
  rw [conjTranspose_smul, hst, mul_smul_comm, smul_mul_assoc, ← smul_add, smul_comm]

lemma hpart1_I (Z : Mx k r) : hpart1 (Hpk k r) (Complex.I • Z) = -hpart2 (Hpk k r) Z := by
  unfold hpart1 hpart2
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  have hc : (1 / (2 * Complex.I) : ℂ) = -((1 / 2 : ℂ) * Complex.I) := by
    rw [one_div, mul_inv, Complex.inv_I]; ring
  rw [conjTranspose_smul, hI, hc]
  simp only [mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, neg_smul, smul_add, smul_sub, smul_neg, smul_smul,
    neg_add, neg_neg, sub_neg_eq_add]

lemma hpart2_I (Z : Mx k r) : hpart2 (Hpk k r) (Complex.I • Z) = hpart1 (Hpk k r) Z := by
  unfold hpart1 hpart2
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  have hc2 : (1 / (2 * Complex.I) : ℂ) * Complex.I = 1 / 2 := by
    rw [one_div, mul_inv, Complex.inv_I]
    linear_combination (-1 / 2 : ℂ) * Complex.I_sq
  rw [conjTranspose_smul, hI]
  simp only [mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, neg_smul, smul_add, smul_sub, smul_neg, smul_smul,
    ← sub_eq_add_neg, hc2]

section abelian₂

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def lam (Φ : Mx k r →L[ℝ] E) (g Z : Mx k r) : E :=
  Φ (g * hpart1 (Hpk k r) Z) + Complex.I • Φ (g * hpart2 (Hpk k r) Z)

lemma real_smul_mx (a : ℝ) (N : Mx k r) : (a : ℂ) • N = a • N := by
  ext i j
  simp [Complex.real_smul]

lemma lam_add (Φ : Mx k r →L[ℝ] E) (g Z W : Mx k r) : lam Φ g (Z + W) = lam Φ g Z + lam Φ g W := by
  unfold lam
  rw [hpart1_add, hpart2_add, mul_add, mul_add, map_add, map_add, smul_add]
  abel

lemma lam_real (Φ : Mx k r →L[ℝ] E) (g Z : Mx k r) (a : ℝ) :
    lam Φ g ((a : ℂ) • Z) = (a : ℂ) • lam Φ g Z := by
  unfold lam
  rw [hpart1_real, hpart2_real, mul_smul_comm, mul_smul_comm, real_smul_mx, real_smul_mx, map_smul, map_smul,
    ← Complex.coe_smul, ← Complex.coe_smul, smul_add, smul_comm Complex.I]

lemma lam_I (Φ : Mx k r →L[ℝ] E) (g Z : Mx k r) :
    lam Φ g (Complex.I • Z) = Complex.I • lam Φ g Z := by
  unfold lam
  rw [hpart1_I, hpart2_I, mul_neg, map_neg, smul_add, smul_smul, Complex.I_mul_I, neg_one_smul]
  abel

lemma lam_smul (Φ : Mx k r →L[ℝ] E) (g Z : Mx k r) (c : ℂ) :
    lam Φ g (c • Z) = c • lam Φ g Z := by
  have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
  rw [hc, add_smul, lam_add, mul_smul, lam_real, lam_real, lam_I, add_smul, mul_smul]

def lamL (Φ : Mx k r →L[ℝ] E) (g : Mx k r) : Mx k r →ₗ[ℂ] E where
  toFun := lam Φ g
  map_add' := lam_add Φ g
  map_smul' c Z := lam_smul Φ g Z c

end abelian₂

theorem transfer_invariance_right : StepRight := by
  intro E _ _ k r i D a b f s' g hD hf hs' hg hgs
  have hgs'G : g * s' ∈ Glev k r i := glev_mul' hg hs'
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf (g * s') ⟨hgs'G, hgs⟩
  have hu := glev_unit hs'
  have hiG := glev_inv hs'
  have hsU : s' ∈ UH (Hpk k r) := by
    have h0 := hs'
    simp only [Glev, Set.mem_setOf_eq] at h0
    exact h0.1
  have hEH : ∀ Z : Mx k r, (∀ t : ℝ, NormedSpace.exp ((t : ℂ) • hpart1 (Hpk k r) Z) ∈ Glev k r i) →
      (∀ t : ℝ, NormedSpace.exp ((t : ℂ) • hpart2 (Hpk k r) Z) ∈ Glev k r i) →
      RdV (hpart1 (Hpk k r) Z) f (g * s') + Complex.I • RdV (hpart2 (Hpk k r) Z) f (g * s') =
        lam (fderiv ℝ F (g * s')) (g * s') Z := by
    intro Z h1 h2
    rw [rdV_ext i _ h1 f F U (g * s') hU hgU hgs'G hF hfF, rdV_ext i _ h2 f F U (g * s') hU hgU hgs'G hF hfF]
    rfl
  have hinj : ∀ c c' : Fin (mdim k r i), posL k r i c = posL k r i c' ↔ c = c' :=
    fun c c' => ⟨posL_inj, congrArg _⟩
  have hconj : s'⁻¹ * Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ) * s' =
      ∑ c, ∑ d, (blk i s'⁻¹ c a * blk i s' b d) • Matrix.single (posL k r i c) (posL k r i d) (1 : ℂ) := by
    ext x y
    have hL : (s'⁻¹ * Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ) * s') x y =
        s'⁻¹ x (posL k r i a) * s' (posL k r i b) y := by
      simp [Matrix.mul_apply, Matrix.single_apply, ite_and, ite_mul]
    rw [hL]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, blk]
    by_cases hx : ∃ c, posL k r i c = x
    · by_cases hy : ∃ d, posL k r i d = y
      · obtain ⟨c0, rfl⟩ := hx
        obtain ⟨d0, rfl⟩ := hy
        simp [hinj, ite_and]
      · push_neg at hy
        have h0 : s' (posL k r i b) y = 0 := by
          rw [glev_col hs' _ y (fun d e => hy d e.symm), (bvec_posL_outer b y (fun d e => hy d e.symm)).1]
        simp [h0, hy]
    · push_neg at hx
      have h0 : s'⁻¹ x (posL k r i a) = 0 := by
        rw [glev_row' hiG x _ (fun c e => hx c e.symm), (bvec_posL_outer a x (fun c e => hx c e.symm)).2]
      simp [h0, hx]
  calc EH k r (posL k r i a) (posL k r i b) (fun x => f (x * s')) g
      = lam (fderiv ℝ F (g * s')) (g * s') (s'⁻¹ * Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ) * s') := by
        show RdV _ (fun x => f (x * s')) g + Complex.I • RdV _ (fun x => f (x * s')) g = _
        rw [rdV_right _ _ _ _ hu.1 hu.2, rdV_right _ _ _ _ hu.1 hu.2, ← hpart1_conj hsU, ← hpart2_conj hsU]
        exact hEH _ (fun t => by rw [hpart1_conj hsU]; exact exp_conj_mem hs' (exp_hpart1_mem i a b) t)
          (fun t => by rw [hpart2_conj hsU]; exact exp_conj_mem hs' (exp_hpart2_mem i a b) t)
    _ = ∑ c, ∑ d, (blk i s'⁻¹ c a * blk i s' b d) •
          lam (fderiv ℝ F (g * s')) (g * s') (Matrix.single (posL k r i c) (posL k r i d) (1 : ℂ)) := by
        rw [hconj]
        change lamL (fderiv ℝ F (g * s')) (g * s')
          (∑ c, ∑ d, (blk i s'⁻¹ c a * blk i s' b d) • Matrix.single (posL k r i c) (posL k r i d) (1 : ℂ)) = _
        simp only [map_sum, map_smul]
        rfl
    _ = _ := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        rw [← hEH _ (exp_hpart1_mem i c d) (exp_hpart2_mem i c d)]
        rfl

end Formalism.FourierDecayAlt.Q.TInvW
end
end

section
namespace Formalism.FourierDecayAlt.Q.TInvW

open Formalism.FourierDecayAlt.Q

theorem qnTInv_of (hCC : ContractionsCovariant) (hP : EabPres) (hG : EabGlLev) (hL : QMinorLeftH) :
    TInvariant :=
  tInvariant_of_contractions hCC hP hG hL transfer_invariance_smooth transfer_invariance_group_mul transfer_invariance_vector transfer_invariance_congruence
    transfer_invariance_right transfer_invariance_restriction

end Formalism.FourierDecayAlt.Q.TInvW
end
