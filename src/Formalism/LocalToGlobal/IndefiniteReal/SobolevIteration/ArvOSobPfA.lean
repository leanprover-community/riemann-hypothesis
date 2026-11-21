import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfSt
import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.IsLowPairZero
import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mult MeasureTheory

namespace Formalism.IndefR.Tow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Classical in

def OrbitDerMult (D : D7) : Prop :=
  ∀ (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) {Ss : D.what₂.Tau → SPar} (M : DSModel V Ss)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsMultMap θ M J χ T →
    ∀ τ, ∀ X ∈ lieAt V τ, ∀ (v : M.Vec) (w : M.sm τ),
      HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v τ)) (w : M.H τ) 0 →
      ∀ x, HasDerivAt (fun t : ℝ => T v (x * oneP θ V τ X t)) (T (Function.update v τ w) x) 0

end Formalism.IndefR.Tow

end
end

section
noncomputable section

open scoped ContDiff

namespace Formalism.IndefR.Tow.OrbStPf

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

def pd (i : Fin N) (f : (Fin N → ℝ) → H) : (Fin N → ℝ) → H :=
  fun p => fderiv ℝ f p (Pi.single i 1)

def pds (L : List (Fin N)) (f : (Fin N → ℝ) → H) : (Fin N → ℝ) → H := L.foldr pd f

@[simp] lemma pds_nil (f : (Fin N → ℝ) → H) : pds [] f = f := rfl

@[simp] lemma pds_cons (i : Fin N) (L : List (Fin N)) (f : (Fin N → ℝ) → H) :
    pds (i :: L) f = pd i (pds L f) := rfl

lemma contDiff_pd (i : Fin N) {f : (Fin N → ℝ) → H} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (pd i f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (m := ∞) (by simp)
  exact hd.clm_apply contDiff_const

lemma contDiff_pds (L : List (Fin N)) {f : (Fin N → ℝ) → H} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (pds L f) := by
  induction L with
  | nil => simpa using hf
  | cons i L ih => simpa only [pds_cons] using contDiff_pd i ih

lemma differentiable_pds (L : List (Fin N)) {f : (Fin N → ℝ) → H} (hf : ContDiff ℝ ∞ f) :
    Differentiable ℝ (pds L f) := by
  exact (contDiff_pds L hf).differentiable (by simp)

lemma pd_hasDerivAt (i : Fin N) {f : (Fin N → ℝ) → H} (p : Fin N → ℝ) (hf : DifferentiableAt ℝ f p) :
    HasDerivAt (fun t : ℝ => f (p + t • Pi.single i 1)) (pd i f p) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => p + t • (Pi.single i 1 : Fin N → ℝ)) (Pi.single i 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i (1 : ℝ) : Fin N → ℝ)).const_add p
  have h2 : HasFDerivAt f (fderiv ℝ f (p + (0 : ℝ) • Pi.single i 1)) (p + (0 : ℝ) • Pi.single i 1) := by
    simpa using hf.hasFDerivAt
  have h3 := h2.comp_hasDerivAt (0 : ℝ) h1
  simpa [pd, Function.comp_def] using h3

lemma pd_eq_deriv (i : Fin N) {f : (Fin N → ℝ) → H} (p : Fin N → ℝ) (hf : DifferentiableAt ℝ f p) :
    pd i f p = deriv (fun t : ℝ => f (p + t • Pi.single i 1)) 0 := by
  exact (pd_hasDerivAt i p hf).deriv.symm

private lemma fderiv_apply_lemma (g : (Fin N → ℝ) → ((Fin N → ℝ) →L[ℝ] H)) (v w p : Fin N → ℝ)
    (hg : DifferentiableAt ℝ g p) : fderiv ℝ (fun q => g q v) p w = fderiv ℝ g p w v := by
  rw [fderiv_clm_apply hg (differentiableAt_const v)]
  simp

lemma pd_comm (i j : Fin N) {f : (Fin N → ℝ) → H} (hf : ContDiff ℝ ∞ f) :
    pd i (pd j f) = pd j (pd i f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (m := ∞) (by simp)
  funext p
  have hs := (hf.contDiffAt (x := p)).isSymmSndFDerivAt
    (by simp <;> first | exact WithTop.coe_le_coe.2 le_top | norm_cast | decide | exact le_top)
  show fderiv ℝ (fun q => fderiv ℝ f q (Pi.single j 1)) p (Pi.single i 1) =
    fderiv ℝ (fun q => fderiv ℝ f q (Pi.single i 1)) p (Pi.single j 1)
  rw [fderiv_apply_lemma _ _ _ _ (hd.differentiable (by simp) p),
    fderiv_apply_lemma _ _ _ _ (hd.differentiable (by simp) p)]
  exact hs _ _

lemma pd_pds (k : Fin N) (L : List (Fin N)) {f : (Fin N → ℝ) → H} (hf : ContDiff ℝ ∞ f) :
    pd k (pds L f) = pds L (pd k f) := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    simp only [pds_cons]
    rw [pd_comm k i (contDiff_pds L hf), ih]

lemma pd_clm (i : Fin N) (A : H →L[ℝ] H) {f : (Fin N → ℝ) → H} (hf : Differentiable ℝ f) :
    pd i (fun p => A (f p)) = fun p => A (pd i f p) := by
  funext p
  have h := (A.hasFDerivAt.comp p (hf p).hasFDerivAt).fderiv
  simp only [pd]
  rw [show (fun q => A (f q)) = A ∘ f from rfl, h]
  rfl

lemma pds_clm (L : List (Fin N)) (A : H →L[ℝ] H) {f : (Fin N → ℝ) → H} (hf : ContDiff ℝ ∞ f) :
    pds L (fun p => A (f p)) = fun p => A (pds L f p) := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    simp only [pds_cons]
    rw [ih, pd_clm i A (differentiable_pds L hf)]

lemma pd_add (i : Fin N) {f g : (Fin N → ℝ) → H} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    pd i (fun p => f p + g p) = fun p => pd i f p + pd i g p := by
  funext p
  simp only [pd]
  have h := ((hf p).hasFDerivAt.add (hg p).hasFDerivAt).fderiv
  exact congrArg (fun L : (Fin N → ℝ) →L[ℝ] H => L (Pi.single i 1)) h

lemma pd_smul (i : Fin N) (c : ℝ) {f : (Fin N → ℝ) → H} (hf : Differentiable ℝ f) :
    pd i (fun p => c • f p) = fun p => c • pd i f p := by
  funext p
  simp only [pd]
  have h := ((hf p).hasFDerivAt.const_smul c).fderiv
  exact congrArg (fun L : (Fin N → ℝ) →L[ℝ] H => L (Pi.single i 1)) h

lemma pds_add (L : List (Fin N)) {f g : (Fin N → ℝ) → H} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    pds L (fun p => f p + g p) = fun p => pds L f p + pds L g p := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    simp only [pds_cons]
    rw [ih, pd_add i (differentiable_pds L hf) (differentiable_pds L hg)]

lemma pds_smul (L : List (Fin N)) (c : ℝ) {f : (Fin N → ℝ) → H} (hf : ContDiff ℝ ∞ f) :
    pds L (fun p => c • f p) = fun p => c • pds L f p := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    simp only [pds_cons]
    rw [ih, pd_smul i c (differentiable_pds L hf)]

lemma update_add_single {i j : Fin N} (hij : i ≠ j) (r : Fin N → ℝ) (s t : ℝ) :
    Function.update (r + t • Pi.single i 1) j s = Function.update r j s + t • Pi.single i 1 := by
  funext k
  by_cases hk : k = j <;> simp [Function.update_apply, hk, Pi.single_apply, Ne.symm hij]

lemma differentiable_update (j : Fin N) (s : ℝ) :
    Differentiable ℝ (fun r : Fin N → ℝ => Function.update r j s) := by
  refine differentiable_pi.2 fun k => ?_
  by_cases hk : k = j
  · subst hk
    simp
  · simpa [Function.update_of_ne hk] using
      (differentiable_apply k : Differentiable ℝ fun r : Fin N → ℝ => r k)

lemma pd_update (i j : Fin N) (hij : i ≠ j) (s : ℝ) {g : (Fin N → ℝ) → H} (hg : Differentiable ℝ g) :
    pd i (fun r => g (Function.update r j s)) = fun r => pd i g (Function.update r j s) := by
  funext r
  rw [pd_eq_deriv i (f := fun r => g (Function.update r j s)) r
      ((hg.comp (differentiable_update j s)) r),
    pd_eq_deriv i _ (hg _)]
  congr 1
  funext t
  simp only [update_add_single hij]

lemma pds_update (L : List (Fin N)) (j : Fin N) (hL : ∀ i ∈ L, i ≠ j) (s : ℝ) {g : (Fin N → ℝ) → H}
    (hg : ContDiff ℝ ∞ g) :
    pds L (fun r => g (Function.update r j s)) = fun r => pds L g (Function.update r j s) := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    simp only [pds_cons]
    rw [ih (fun k hk => hL k (by simp [hk])),
      pd_update i j (hL i (by simp)) s (differentiable_pds L hg)]

end Formalism.IndefR.Tow.OrbStPf

end
end

section
noncomputable section

open scoped ContDiff
open Formalism.L2.Theta

namespace Formalism.IndefR.Tow.OrbStPf

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (ρ : Matrix (Fin n) (Fin n) ℂ → (E →L[ℂ] E)) (Lie U : Set (Matrix (Fin n) (Fin n) ℂ))

section SV

variable {ρ Lie}

lemma smoothVec_zero : SmoothVec Lie ρ 0 := by
  intro k Xs _
  simp only [map_zero]
  exact contDiff_const

lemma smoothVec_add {a b : E} (ha : SmoothVec Lie ρ a) (hb : SmoothVec Lie ρ b) : SmoothVec Lie ρ (a + b) := by
  intro k Xs hXs
  simp only [map_add]
  exact (ha k Xs hXs).add (hb k Xs hXs)

lemma smoothVec_smul (c : ℂ) {a : E} (ha : SmoothVec Lie ρ a) : SmoothVec Lie ρ (c • a) := by
  intro k Xs hXs
  simp only [map_smul]
  exact (ha k Xs hXs).const_smul c

lemma smoothVec_rsmul (c : ℝ) {a : E} (ha : SmoothVec Lie ρ a) : SmoothVec Lie ρ (c • a) := by
  rw [← Complex.coe_smul]
  exact smoothVec_smul (c : ℂ) ha


end SV

variable {ρ Lie U}
variable (hU1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ U) (hUm : ∀ a ∈ U, ∀ b ∈ U, a * b ∈ U)
  (hρ : ∀ a ∈ U, ∀ b ∈ U, ρ (a * b) = (ρ a).comp (ρ b))
  (hexp : ∀ Y ∈ Lie, ∀ t : ℝ, NormedSpace.exp (t • Y) ∈ U)

include hU1 hUm in
lemma list_prod_mem (l : List (Matrix (Fin n) (Fin n) ℂ)) (hl : ∀ a ∈ l, a ∈ U) : l.prod ∈ U := by
  induction l with
  | nil => simpa using hU1
  | cons a l ih =>
    rw [List.prod_cons]
    exact hUm a (hl a (by simp)) _ (ih (fun b hb => hl b (by simp [hb])))

include hU1 hUm hexp in
lemma prod_drop_mem {N : ℕ} (Z : Fin N → Matrix (Fin n) (Fin n) ℂ) (hZ : ∀ i, Z i ∈ Lie) (r : Fin N → ℝ) (j : ℕ) :
    ((List.ofFn fun i => NormedSpace.exp (r i • Z i)).drop j).prod ∈ U := by
  refine list_prod_mem hU1 hUm _ ?_
  intro a ha
  have ha' := List.mem_of_mem_drop ha
  simp only [List.mem_ofFn] at ha'
  obtain ⟨i, rfl⟩ := ha'
  exact hexp _ (hZ i) _

include hU1 hUm hρ hexp in

lemma smoothVec_rep_exp {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ Lie) (s : ℝ) {w : E} (hw : SmoothVec Lie ρ w) :
    SmoothVec Lie ρ (ρ (NormedSpace.exp (s • X)) w) := by
  intro k Xs hXs
  have hX' : ∀ i, (Fin.snoc Xs X : Fin (k + 1) → Matrix (Fin n) (Fin n) ℂ) i ∈ Lie := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hX
    · simpa using hXs j
  have hsn : ContDiff ℝ ∞ (fun t : Fin k → ℝ => (Fin.snoc t s : Fin (k + 1) → ℝ)) := by
    refine contDiff_pi.2 fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using (contDiff_const : ContDiff ℝ ∞ fun _ : Fin k → ℝ => s)
    · simpa using (contDiff_pi.1 contDiff_id j : ContDiff ℝ ∞ fun t : Fin k → ℝ => t j)
  have h := (hw (k + 1) (Fin.snoc Xs X) hX').comp hsn
  convert h using 1
  funext t
  simp only [Function.comp_apply]
  rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  have hP : (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod ∈ U := by
    refine list_prod_mem hU1 hUm _ (fun a ha => ?_)
    simp only [List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    exact hexp _ (hXs i) _
  rw [hρ _ hP _ (hexp _ hX _)]
  rfl

variable (ρ) in

def orb {N : ℕ} (Z : Fin N → Matrix (Fin n) (Fin n) ℂ) (u : E) (j : ℕ) (r : Fin N → ℝ) : E :=
  ρ (((List.ofFn fun i => NormedSpace.exp (r i • Z i)).drop j).prod) u

def mask {N : ℕ} (j : ℕ) (r : Fin N → ℝ) : Fin N → ℝ := fun i => if i.val < j then 0 else r i

lemma prod_mask {N : ℕ} (Z : Fin N → Matrix (Fin n) (Fin n) ℂ) (j : ℕ) (r : Fin N → ℝ) :
    (List.ofFn fun i => NormedSpace.exp (mask j r i • Z i)).prod =
      ((List.ofFn fun i => NormedSpace.exp (r i • Z i)).drop j).prod := by
  have hd : (List.ofFn fun i => NormedSpace.exp (mask j r i • Z i)).drop j =
      (List.ofFn fun i => NormedSpace.exp (r i • Z i)).drop j := by
    apply List.ext_getElem
    · simp
    · intro k h1 h2
      simp only [List.getElem_drop, List.getElem_ofFn, mask]
      rw [if_neg (by simp)]
  have ht : ((List.ofFn fun i => NormedSpace.exp (mask j r i • Z i)).take j).prod = 1 := by
    apply List.prod_eq_one
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
    have hkj : k < j := by simp at hk; omega
    simp [List.getElem_take, mask, hkj]
  rw [← List.prod_take_mul_prod_drop (List.ofFn fun i => NormedSpace.exp (mask j r i • Z i)) j, ht, one_mul, hd]

lemma contDiff_mask {N : ℕ} (j : ℕ) : ContDiff ℝ ∞ (mask (N := N) j) := by
  refine contDiff_pi.2 fun i => ?_
  by_cases h : i.val < j
  · simp only [mask, h, if_true]
    exact contDiff_const
  · simp only [mask, h, if_false]
    exact contDiff_pi.1 contDiff_id i

lemma contDiff_orb {N : ℕ} (Z : Fin N → Matrix (Fin n) (Fin n) ℂ) (hZ : ∀ i, Z i ∈ Lie) {u : E}
    (hu : SmoothVec Lie ρ u) (j : ℕ) : ContDiff ℝ ∞ (orb ρ Z u j) := by
  have h := (hu N Z hZ).comp (contDiff_mask (N := N) j)
  convert h using 1
  funext r
  simp only [orb, Function.comp_apply, prod_mask]

include hU1 hUm hρ hexp in
lemma orb_update {N : ℕ} (Z : Fin N → Matrix (Fin n) (Fin n) ℂ) (hZ : ∀ i, Z i ∈ Lie) (u : E) (j : ℕ)
    (hj : j < N) (r : Fin N → ℝ) (s : ℝ) :
    orb ρ Z u j (Function.update r ⟨j, hj⟩ s) = ρ (NormedSpace.exp (s • Z ⟨j, hj⟩)) (orb ρ Z u (j + 1) r) := by
  simp only [orb]
  have hlen : j < (List.ofFn fun i => NormedSpace.exp (Function.update r ⟨j, hj⟩ s i • Z i)).length := by
    simpa using hj
  rw [List.drop_eq_getElem_cons hlen, List.prod_cons]
  have hdrop : (List.ofFn fun i => NormedSpace.exp (Function.update r ⟨j, hj⟩ s i • Z i)).drop (j + 1) =
      (List.ofFn fun i => NormedSpace.exp (r i • Z i)).drop (j + 1) := by
    apply List.ext_getElem
    · simp
    · intro k h1 h2
      simp only [List.getElem_drop, List.getElem_ofFn]
      rw [Function.update_apply, if_neg]
      intro h
      simp only [Fin.mk.injEq] at h
      omega
  rw [hdrop, List.getElem_ofFn, Function.update_apply, if_pos rfl,
    hρ _ (hexp _ (hZ _) _) _ (prod_drop_mem hU1 hUm hexp Z hZ r (j + 1))]
  rfl

lemma orb_last {k : ℕ} (Z : Fin (k + 1) → Matrix (Fin n) (Fin n) ℂ) (u : E) (r : Fin (k + 1) → ℝ) :
    orb ρ Z u k r = ρ (NormedSpace.exp (r (Fin.last k) • Z (Fin.last k))) u := by
  simp only [orb]
  rw [List.ofFn_succ', List.concat_eq_append, List.drop_left' (by simp), List.prod_singleton]

include hU1 hUm hρ hexp in
theorem word_pds {k : ℕ} (l : List (Matrix (Fin n) (Fin n) ℂ)) (hl : l.length = k)
    (Z : Fin (k + 1) → Matrix (Fin n) (Fin n) ℂ) (hZ : ∀ i, Z i ∈ Lie)
    (hZl : ∀ (i : Fin (k + 1)) (h : i.val < k), Z i = l[i.val]'(by omega)) :
    ∀ d j, j + d = k → ∃ L : List (Fin (k + 1)), (∀ i ∈ L, j ≤ i.val ∧ i.val < k) ∧
      ∀ u, SmoothVec Lie ρ u → ∀ r : Fin (k + 1) → ℝ, (∀ i : Fin (k + 1), j ≤ i.val → i.val < k → r i = 0) →
        (l.drop j).foldr (dRep ρ) (orb ρ Z u k r) = pds L (orb ρ Z u j) r := by
  intro d
  induction d with
  | zero =>
    intro j hj
    refine ⟨[], by simp, ?_⟩
    intro u _ r _
    obtain rfl : j = k := by omega
    have h0 : l.drop j = [] := List.drop_eq_nil_of_le (by omega)
    rw [h0, List.foldr_nil, pds_nil]
  | succ d ih =>
    intro j hj
    obtain ⟨L', hL'1, hL'2⟩ := ih (j + 1) (by omega)
    have hjk : j < k := by omega
    refine ⟨⟨j, by omega⟩ :: L', ?_, ?_⟩
    · intro i hi
      rcases List.mem_cons.1 hi with h | h
      · subst h
        exact ⟨le_refl _, hjk⟩
      · have := hL'1 i h
        exact ⟨by omega, this.2⟩
    · intro u hu r hr
      have hjl : j < l.length := by omega
      rw [List.drop_eq_getElem_cons hjl, List.foldr_cons,
        hL'2 u hu r (fun i h1 h2 => hr i (by omega) h2), pds_cons]
      have hne : ∀ i ∈ L', i ≠ (⟨j, by omega⟩ : Fin (k + 1)) := by
        intro i hi h
        have := (hL'1 i hi).1
        rw [h] at this
        simp at this
      have hF : ContDiff ℝ ∞ (pds L' (orb ρ Z u j)) := contDiff_pds L' (contDiff_orb Z hZ hu j)
      have hdiff : DifferentiableAt ℝ (pds L' (orb ρ Z u j)) r := hF.differentiable (by simp) r
      rw [pd_eq_deriv _ r hdiff]
      have hZj : Z ⟨j, by omega⟩ = l[j] := hZl ⟨j, by omega⟩ hjk
      have hfun : (fun t : ℝ => pds L' (orb ρ Z u j) (r + t • Pi.single (⟨j, by omega⟩ : Fin (k + 1)) (1 : ℝ))) =
          fun t => ρ (NormedSpace.exp (t • Z ⟨j, by omega⟩)) (pds L' (orb ρ Z u (j + 1)) r) := by
        funext t
        have hup : r + t • Pi.single (⟨j, by omega⟩ : Fin (k + 1)) (1 : ℝ) = Function.update r ⟨j, by omega⟩ t := by
          funext i
          by_cases h : i = ⟨j, by omega⟩
          · subst h
            simp [hr ⟨j, by omega⟩ (le_refl j) hjk]
          · simp [h, Pi.single_apply, Function.update_apply]
        have h1 : pds L' (orb ρ Z u j) (Function.update r ⟨j, by omega⟩ t) =
            pds L' (fun r' => orb ρ Z u j (Function.update r' ⟨j, by omega⟩ t)) r := by
          rw [pds_update L' _ hne t (contDiff_orb Z hZ hu j)]
        have h2 : (fun r' => orb ρ Z u j (Function.update r' ⟨j, by omega⟩ t)) =
            fun r' => ((ρ (NormedSpace.exp (t • Z ⟨j, by omega⟩))).restrictScalars ℝ) (orb ρ Z u (j + 1) r') := by
          funext r'
          exact orb_update hU1 hUm hρ hexp Z hZ u j (by omega) r' t
        rw [hup, h1, h2, pds_clm L' _ (contDiff_orb Z hZ hu (j + 1))]
        rfl
      (rw [hfun, hZj]) <;> rfl

lemma orb_zero_split {k : ℕ} (Z : Fin (k + 1) → Matrix (Fin n) (Fin n) ℂ) (u : E) (r : Fin (k + 1) → ℝ) :
    orb ρ Z u 0 r = ρ ((List.ofFn fun i : Fin k => NormedSpace.exp (r i.castSucc • Z i.castSucc)).prod *
      NormedSpace.exp (r (Fin.last k) • Z (Fin.last k))) u := by
  simp only [orb, List.drop_zero]
  rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton]

include hU1 hUm hρ hexp in

lemma pd_last_orb {k : ℕ} (Z : Fin (k + 1) → Matrix (Fin n) (Fin n) ℂ) (hZ : ∀ i, Z i ∈ Lie) {u w : E}
    (hu : SmoothVec Lie ρ u) (hd : HasDerivAt (fun t : ℝ => ρ (NormedSpace.exp (t • Z (Fin.last k))) u) w 0) :
    pd (Fin.last k) (orb ρ Z u 0) = orb ρ Z w 0 := by
  funext r
  have hdiff : DifferentiableAt ℝ (orb ρ Z u 0) r :=
    (contDiff_orb Z hZ hu 0).differentiable (by simp) r
  rw [pd_eq_deriv _ r hdiff]
  have hP : (List.ofFn fun i : Fin k => NormedSpace.exp (r i.castSucc • Z i.castSucc)).prod ∈ U := by
    refine list_prod_mem hU1 hUm _ (fun a ha => ?_)
    simp only [List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    exact hexp _ (hZ _) _
  have hE : ∀ s : ℝ, NormedSpace.exp (s • Z (Fin.last k)) ∈ U := fun s => hexp _ (hZ _) _
  have hfun : (fun t : ℝ => orb ρ Z u 0 (r + t • Pi.single (Fin.last k) 1)) =
      fun t => ((ρ (List.ofFn fun i : Fin k => NormedSpace.exp (r i.castSucc • Z i.castSucc)).prod).comp
        (ρ (NormedSpace.exp (r (Fin.last k) • Z (Fin.last k))))) (ρ (NormedSpace.exp (t • Z (Fin.last k))) u) := by
    funext t
    rw [orb_zero_split]
    have hc : ∀ i : Fin k, (r + t • Pi.single (Fin.last k) (1 : ℝ) : Fin (k + 1) → ℝ) i.castSucc = r i.castSucc := by
      intro i
      simp [Pi.single_apply, Fin.castSucc_ne_last]
    have hl : (r + t • Pi.single (Fin.last k) (1 : ℝ) : Fin (k + 1) → ℝ) (Fin.last k) = r (Fin.last k) + t := by simp
    simp only [hc, hl]
    rw [add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl (Z (Fin.last k))).smul_left _).smul_right _),
      ← mul_assoc, hρ _ (hUm _ hP _ (hE _)) _ (hE _), hρ _ hP _ (hE _)]
    rfl
  rw [hfun]
  have hD : HasDerivAt (fun t : ℝ => ((ρ (List.ofFn fun i : Fin k => NormedSpace.exp (r i.castSucc • Z i.castSucc)).prod).comp
        (ρ (NormedSpace.exp (r (Fin.last k) • Z (Fin.last k))))) (ρ (NormedSpace.exp (t • Z (Fin.last k))) u))
      (((ρ (List.ofFn fun i : Fin k => NormedSpace.exp (r i.castSucc • Z i.castSucc)).prod).comp
        (ρ (NormedSpace.exp (r (Fin.last k) • Z (Fin.last k))))) w) 0 := ((((ρ (List.ofFn fun i : Fin k => NormedSpace.exp (r i.castSucc • Z i.castSucc)).prod).comp
        (ρ (NormedSpace.exp (r (Fin.last k) • Z (Fin.last k))))).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt
        (0 : ℝ) hd
  (rw [hD.deriv, orb_zero_split, hρ _ hP _ (hE _)]) <;> rfl

include hU1 hUm hρ hexp in

lemma word_eval (l : List (Matrix (Fin n) (Fin n) ℂ)) (hl : ∀ Y ∈ l, Y ∈ Lie)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ Lie) :
    ∃ (Z : Fin (l.length + 1) → Matrix (Fin n) (Fin n) ℂ) (L : List (Fin (l.length + 1))), (∀ i, Z i ∈ Lie) ∧
      Z (Fin.last _) = X ∧ ∀ v, SmoothVec Lie ρ v → ∀ t : ℝ,
        l.foldr (dRep ρ) (ρ (NormedSpace.exp (t • X)) v) = pds L (orb ρ Z v 0) (t • Pi.single (Fin.last _) 1) := by
  let Z : Fin (l.length + 1) → Matrix (Fin n) (Fin n) ℂ := fun i => if h : i.val < l.length then l[i.val] else X
  have hZ : ∀ i, Z i ∈ Lie := by
    intro i
    simp only [Z]
    split_ifs with h
    · exact hl _ (by simp)
    · exact hX
  have hZl : ∀ (i : Fin (l.length + 1)) (h : i.val < l.length), Z i = l[i.val]'(by omega) := by
    intro i h
    simp only [Z, dif_pos h]
  obtain ⟨L, -, hL⟩ := word_pds hU1 hUm hρ hexp l rfl Z hZ hZl l.length 0 (by simp)
  refine ⟨Z, L, hZ, by simp [Z], ?_⟩
  intro v hv t
  have hr : ∀ i : Fin (l.length + 1), 0 ≤ i.val → i.val < l.length →
      (t • Pi.single (Fin.last l.length) (1 : ℝ)) i = 0 := by
    intro i _ h
    have : i ≠ Fin.last _ := by
      intro h'
      rw [h'] at h
      simp at h
    simp [Pi.single_apply, this]
  have := hL v hv _ hr
  rw [List.drop_zero] at this
  rw [← this, orb_last]
  simp [Z]

include hU1 hUm hρ hexp in

theorem word_deriv (hρ1 : ρ 1 = 1) (l : List (Matrix (Fin n) (Fin n) ℂ)) (hl : ∀ Y ∈ l, Y ∈ Lie)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ Lie) {u w : E} (hu : SmoothVec Lie ρ u) (hw : SmoothVec Lie ρ w)
    (hd : HasDerivAt (fun t : ℝ => ρ (NormedSpace.exp (t • X)) u) w 0) :
    HasDerivAt (fun t : ℝ => l.foldr (dRep ρ) (ρ (NormedSpace.exp (t • X)) u)) (l.foldr (dRep ρ) w) 0 := by
  obtain ⟨Z, L, hZ, hZX, hL⟩ := word_eval hU1 hUm hρ hexp l hl hX
  have hfun : (fun t : ℝ => l.foldr (dRep ρ) (ρ (NormedSpace.exp (t • X)) u)) =
      fun t => pds L (orb ρ Z u 0) (0 + t • Pi.single (Fin.last _) 1) := by
    funext t
    rw [hL u hu t, zero_add]
  rw [hfun]
  have hF : ContDiff ℝ ∞ (pds L (orb ρ Z u 0)) := contDiff_pds L (contDiff_orb Z hZ hu 0)
  have h1 := pd_hasDerivAt (Fin.last _) (0 : Fin (l.length + 1) → ℝ) (hF.differentiable (by simp) 0)
  convert h1 using 1
  have hd' : HasDerivAt (fun t : ℝ => ρ (NormedSpace.exp (t • Z (Fin.last _))) u) w 0 := by
    rw [hZX]
    exact hd
  rw [pd_pds _ L (contDiff_orb Z hZ hu 0), pd_last_orb hU1 hUm hρ hexp Z hZ hu hd']
  have := hL w hw 0
  rw [zero_smul, zero_smul, NormedSpace.exp_zero, hρ1, ContinuousLinearMap.one_apply] at this
  exact this

include hU1 hUm hρ hexp in

theorem word_lin (hρ1 : ρ 1 = 1) (l : List (Matrix (Fin n) (Fin n) ℂ)) (hl : ∀ Y ∈ l, Y ∈ Lie)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ Lie) {a b : E} (ha : SmoothVec Lie ρ a) (hb : SmoothVec Lie ρ b)
    (c : ℝ) : l.foldr (dRep ρ) (a + c • b) = l.foldr (dRep ρ) a + c • l.foldr (dRep ρ) b := by
  obtain ⟨Z, L, hZ, -, hL⟩ := word_eval hU1 hUm hρ hexp l hl hX
  have key : ∀ v, SmoothVec Lie ρ v → l.foldr (dRep ρ) v = pds L (orb ρ Z v 0) 0 := by
    intro v hv
    have := hL v hv 0
    rw [zero_smul, zero_smul, NormedSpace.exp_zero, hρ1, ContinuousLinearMap.one_apply] at this
    exact this
  have hab : SmoothVec Lie ρ (a + c • b) := smoothVec_add ha (smoothVec_rsmul c hb)
  rw [key _ hab, key _ ha, key _ hb]
  have horb : orb ρ Z (a + c • b) 0 = fun r => orb ρ Z a 0 r + c • orb ρ Z b 0 r := by
    funext r
    simp only [orb, map_add, ContinuousLinearMap.map_smul_of_tower]
  rw [horb, pds_add L (contDiff_orb Z hZ ha 0) ((contDiff_orb Z hZ hb 0).const_smul c),
    pds_smul L c (contDiff_orb Z hZ hb 0)]

end Formalism.IndefR.Tow.OrbStPf

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mult MeasureTheory
open scoped ContDiff Matrix Topology
open Asymptotics

namespace Formalism.IndefR.Tow.OrbStPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem conj_mem {n : ℕ} (J G fr g : Matrix (Fin n) (Fin n) ℂ) (hfr : IsUnit fr) (hJ : frᴴ * J * fr = G)
    (hg : gᴴ * G * g = G) : (fr * g * fr⁻¹)ᴴ * J * (fr * g * fr⁻¹) = J := by
  have hd : IsUnit fr.det := (Matrix.isUnit_iff_isUnit_det fr).mp hfr
  have h1 : fr * fr⁻¹ = 1 := Matrix.mul_nonsing_inv fr hd
  have h2 : (fr⁻¹)ᴴ * frᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  calc (fr * g * fr⁻¹)ᴴ * J * (fr * g * fr⁻¹)
      = (fr⁻¹)ᴴ * (gᴴ * (frᴴ * J * fr) * g) * fr⁻¹ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (fr⁻¹)ᴴ * (frᴴ * J * fr) * fr⁻¹ := by rw [hJ, hg]
    _ = ((fr⁻¹)ᴴ * frᴴ) * J * (fr * fr⁻¹) := by simp only [Matrix.mul_assoc]
    _ = J := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem exp_form {n : ℕ} (G X : Matrix (Fin n) (Fin n) ℂ) (hG : IsUnit G)
    (hX : Xᴴ * G + G * X = 0) : (NormedSpace.exp X)ᴴ * G * NormedSpace.exp X = G := by

  have hGd : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).1 hG
  have hGG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hGd
  have hGG' : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hGd
  have hXc : G * (-X) * G⁻¹ = Xᴴ := by
    have h1 : Xᴴ * G = -(G * X) := eq_neg_of_add_eq_zero_left hX
    calc G * (-X) * G⁻¹ = -(G * X) * G⁻¹ := by rw [Matrix.mul_neg]
      _ = Xᴴ * G * G⁻¹ := by rw [h1]
      _ = Xᴴ := by rw [Matrix.mul_assoc, hGG', Matrix.mul_one]
  have hexpH : (NormedSpace.exp X)ᴴ = G * NormedSpace.exp (-X) * G⁻¹ := by
    rw [← Matrix.exp_conjTranspose, ← hXc, Matrix.exp_conj G (-X) hG]
  have hneg : NormedSpace.exp (-X) * NormedSpace.exp X = 1 := by
    rw [← Matrix.exp_add_of_commute (-X) X (Commute.neg_left (Commute.refl X)), neg_add_cancel,
      NormedSpace.exp_zero]
  rw [hexpH]
  calc G * NormedSpace.exp (-X) * G⁻¹ * G * NormedSpace.exp X
      = G * (NormedSpace.exp (-X) * NormedSpace.exp X) := by
        simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc G⁻¹ G, hGG, Matrix.one_mul]
    _ = G := by rw [hneg, Matrix.mul_one]

theorem uh_mul {n : ℕ} (G g h : Matrix (Fin n) (Fin n) ℂ) (hg : g ∈ Formalism.QuantumDeterminants.UH G) (hh : h ∈ Formalism.QuantumDeterminants.UH G) :
    g * h ∈ Formalism.QuantumDeterminants.UH G := by

  have h1 : gᴴ * G * g = G := hg
  have h2 : hᴴ * G * h = G := hh
  show (g * h)ᴴ * G * (g * h) = G
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * G * (g * h) = hᴴ * (gᴴ * G * g) * h := by simp only [Matrix.mul_assoc]
    _ = G := by rw [h1, h2]

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem gram_unit (M : DSModel V S) (τ : D.what₂.Tau) : IsUnit (gramAt D V τ) := by

  have hJ : Formalism.REAL.Jm (M.ε τ) * Formalism.REAL.Jm (M.ε τ) = 1 := by
    simp only [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hJu : IsUnit (Formalism.REAL.Jm (M.ε τ)) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hJ)
  have hfr := M.fr_unit τ
  have hfrH : IsUnit (M.fr τ)ᴴ := (Matrix.isUnit_iff_isUnit_det _).2 (by
    rw [Matrix.det_conjTranspose]; exact ((Matrix.isUnit_iff_isUnit_det _).1 hfr).star)
  rw [← M.fr_gram τ]
  exact (hfrH.mul hJu).mul hfr

theorem exp_mem_UH (M : DSModel V S) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hX : X ∈ lieAt V τ) (t : ℝ) : NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by

  have hG := gram_unit M τ
  have h1 : Xᴴ * gramAt D V τ + gramAt D V τ * X = 0 := hX
  show (NormedSpace.exp (t • X))ᴴ * gramAt D V τ * NormedSpace.exp (t • X) = gramAt D V τ
  refine exp_form _ _ hG ?_
  rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1,
    smul_zero]

theorem rep_mul (M : DSModel V S) (τ : D.what₂.Tau) (g h : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hh : h ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    M.rep τ (g * h) = (M.rep τ g).comp (M.rep τ h) := by

  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hfr' : (M.fr τ)⁻¹ * M.fr τ = 1 := Matrix.nonsing_inv_mul _ hd
  show M.σ τ (M.fr τ * (g * h) * (M.fr τ)⁻¹) =
    (M.σ τ (M.fr τ * g * (M.fr τ)⁻¹)).comp (M.σ τ (M.fr τ * h * (M.fr τ)⁻¹))
  have e : M.fr τ * (g * h) * (M.fr τ)⁻¹ =
      (M.fr τ * g * (M.fr τ)⁻¹) * (M.fr τ * h * (M.fr τ)⁻¹) := by
    calc M.fr τ * (g * h) * (M.fr τ)⁻¹
        = M.fr τ * g * ((M.fr τ)⁻¹ * M.fr τ) * h * (M.fr τ)⁻¹ := by
          rw [hfr', Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e]
  have hmem : ∀ x ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * x * (M.fr τ)⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) := fun x hx =>
    conj_mem (Formalism.REAL.Jm (M.ε τ)) (gramAt D V τ) (M.fr τ) x (M.fr_unit τ) (M.fr_gram τ) hx
  exact (M.ds τ).2.2.1.1.2 _ (hmem g hg) _ (hmem h hh)

theorem rep_one (M : DSModel V S) (τ : D.what₂.Tau) : M.rep τ 1 = 1 := by

  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  show M.σ τ (M.fr τ * 1 * (M.fr τ)⁻¹) = 1
  rw [Matrix.mul_one, Matrix.mul_nonsing_inv _ hd]
  exact (M.ds τ).2.2.1.1.1

open Classical in

theorem orbit_eq (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M)
    (hT : IsMultMap θ M J χ T) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hX : X ∈ lieAt V τ)
    (v : M.Vec) (t : ℝ) (hs : M.rep τ (NormedSpace.exp (t • X)) (v τ) ∈ M.sm τ) (x : GA D V) :
    T v (x * oneP θ V τ X t) = T (Function.update v τ ⟨_, hs⟩) x := by

  have h := hT.equiv τ _ (exp_mem_UH M τ X hX t) v ⟨_, hs⟩ rfl
  first
    | (rw [h]; rfl)
    | (refine Eq.trans ?_ (congrFun h x).symm; rfl)
    | (convert (congrFun h x).symm using 1)


end Formalism.IndefR.Tow.OrbStPf

namespace Formalism.IndefR.Tow

open OrbStPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar


end Formalism.IndefR.Tow

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mult
  MeasureTheory Matrix Filter Topology
open scoped ContDiff

namespace Formalism.IndefR.Tow.SobPf

section Gen

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem one_mem_UH (G : Matrix (Fin n) (Fin n) ℂ) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.QuantumDeterminants.UH G := by
  show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * G * 1 = G
  simp

theorem zero_mem_lieG (G : Matrix (Fin n) (Fin n) ℂ) : (0 : Matrix (Fin n) (Fin n) ℂ) ∈ lieG G := by
  show (0 : Matrix (Fin n) (Fin n) ℂ)ᴴ * G + G * 0 = 0
  simp

theorem expS_mem_UH {G X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH G := by
  have h := CCRuleCW.lie_smul G X hX t
  rw [Complex.coe_smul] at h
  exact CCRuleCW.exp_mem_UH G (t • X) h

theorem mul_mem_UH₂ (G : Matrix (Fin n) (Fin n) ℂ) :
    ∀ a ∈ Formalism.QuantumDeterminants.UH G, ∀ b ∈ Formalism.QuantumDeterminants.UH G, a * b ∈ Formalism.QuantumDeterminants.UH G := by
  intro a ha b hb
  have ha' : aᴴ * G * a = G := ha
  have hb' : bᴴ * G * b = G := hb
  show (a * b)ᴴ * G * (a * b) = G
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * G * (a * b) = bᴴ * (aᴴ * G * a) * b := by simp only [Matrix.mul_assoc]
    _ = G := by rw [ha', hb']



theorem smooth_oneProd {G : Matrix (Fin n) (Fin n) ℂ} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hπ : IsGRep G π) {w : H} (hw : SmoothVec (lieG G) π w) :
    ∀ {d : ℕ} (Y : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i, Y i ∈ lieG G) → ∀ t : Fin d → ℝ,
      SmoothVec (lieG G) π (π (oneProd Y t) w) ∧ oneProd Y t ∈ Formalism.QuantumDeterminants.UH G := by
  intro d
  induction d with
  | zero =>
    intro Y _ t
    simp only [oneProd, List.ofFn_zero, List.prod_nil, hπ.1]
    exact ⟨hw, one_mem_UH G⟩
  | succ d ih =>
    intro Y hY t
    have e : oneProd Y t = NormedSpace.exp (t 0 • Y 0) * oneProd (fun i => Y i.succ) (fun i => t i.succ) := by
      simp [oneProd, List.ofFn_succ]
    obtain ⟨h1, h2⟩ := ih (fun i => Y i.succ) (fun i => hY _) (fun i => t i.succ)
    rw [e, hπ.2.1 _ (expS_mem_UH (hY 0) _) _ h2]
    exact ⟨OrbStPf.smoothVec_rep_exp (one_mem_UH G) (mul_mem_UH₂ G) hπ.2.1 (fun Y hY t => expS_mem_UH hY t) (hY 0) (t 0) h1,
      mul_mem_UH₂ G _ (expS_mem_UH (hY 0) _) _ h2⟩

end Gen

section Append

theorem append_line {N d : ℕ} (r : Fin N → ℝ) (t : Fin d → ℝ) (i : Fin N) (s : ℝ) :
    Fin.append (r + s • Pi.single i 1) t = Fin.append r t + s • Pi.single (Fin.castAdd d i) 1 := by
  funext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp [Pi.single_apply, Fin.castAdd_inj]
  · have hne : (Fin.natAdd N j : Fin (N + d)) ≠ Fin.castAdd d i := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.coe_natAdd, Fin.coe_castAdd] at this
      omega
    simp [Pi.single_apply, hne]

theorem contDiff_append_left {N d : ℕ} (t : Fin d → ℝ) : ContDiff ℝ ∞ (fun r : Fin N → ℝ => Fin.append r t) := by
  refine contDiff_pi.2 fun j => ?_
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp only [Fin.append_left]
    exact contDiff_apply ℝ ℝ j
  · simp only [Fin.append_right]
    exact contDiff_const

theorem continuous_append_right {N d : ℕ} (r : Fin N → ℝ) :
    Continuous (fun t : Fin d → ℝ => Fin.append r t) := by
  refine continuous_pi fun j => ?_
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp only [Fin.append_left]
    exact continuous_const
  · simp only [Fin.append_right]
    exact continuous_apply j

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem pd_append {N d : ℕ} (f : (Fin (N + d) → ℝ) → E) (hf : Differentiable ℝ f) (t : Fin d → ℝ) (i : Fin N) :
    OrbStPf.pd i (fun r => f (Fin.append r t)) = fun r => OrbStPf.pd (Fin.castAdd d i) f (Fin.append r t) := by
  funext r
  simp only [OrbStPf.pd]
  have hg : Differentiable ℝ (fun r : Fin N → ℝ => Fin.append r t) :=
    (contDiff_infty_iff_fderiv.1 (contDiff_append_left t)).1
  rw [fderiv_comp' r (hf _) (hg r), ContinuousLinearMap.comp_apply]
  congr 1
  have h1 : HasDerivAt (fun s : ℝ => Fin.append (r + s • (Pi.single i 1 : Fin N → ℝ)) t)
      (fderiv ℝ (fun r : Fin N → ℝ => Fin.append r t) r (Pi.single i 1)) 0 := by
    have hl : HasDerivAt (fun s : ℝ => r + s • (Pi.single i 1 : Fin N → ℝ)) (Pi.single i 1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i 1 : Fin N → ℝ)).const_add r
    have h3 := (hg (r + (0 : ℝ) • (Pi.single i 1 : Fin N → ℝ))).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
    rw [zero_smul, add_zero] at h3
    exact h3
  have h2 : HasDerivAt (fun s : ℝ => Fin.append (r + s • (Pi.single i 1 : Fin N → ℝ)) t)
      (Pi.single (Fin.castAdd d i) 1) 0 := by
    simp only [append_line]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
      (Pi.single (Fin.castAdd d i) 1 : Fin (N + d) → ℝ)).const_add (Fin.append r t)
  exact h1.unique h2

private theorem pds_contDiff_lemma {N : ℕ} (L : List (Fin N)) (f : (Fin N → ℝ) → E)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (OrbStPf.pds L f) := by
  induction L with
  | nil => exact hf
  | cons a L ih =>
    show ContDiff ℝ ∞ (fun p => fderiv ℝ (OrbStPf.pds L f) p (Pi.single a 1))
    exact (contDiff_infty_iff_fderiv.1 ih).2.clm_apply contDiff_const

theorem pds_append {N d : ℕ} (L : List (Fin N)) (f : (Fin (N + d) → ℝ) → E) (hf : ContDiff ℝ ∞ f)
    (t : Fin d → ℝ) :
    OrbStPf.pds L (fun r => f (Fin.append r t)) =
      fun r => OrbStPf.pds (L.map (Fin.castAdd d)) f (Fin.append r t) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    have hg : ContDiff ℝ ∞ (OrbStPf.pds (L.map (Fin.castAdd d)) f) := pds_contDiff_lemma _ f hf
    show OrbStPf.pd a (OrbStPf.pds L fun r => f (Fin.append r t)) =
      fun r => OrbStPf.pd (Fin.castAdd d a) (OrbStPf.pds (L.map (Fin.castAdd d)) f) (Fin.append r t)
    rw [ih]
    exact pd_append _ (contDiff_infty_iff_fderiv.1 hg).1 t a

end Append

theorem foldCont_holds : FoldCont := by
  intro n H _ _ G π hπ w hw l hl d Y hY
  have hexp : ∀ Y ∈ lieG G, ∀ t : ℝ, NormedSpace.exp (t • Y) ∈ Formalism.QuantumDeterminants.UH G := fun Y hY t => expS_mem_UH hY t
  obtain ⟨Z, L, hZ, -, hval⟩ := OrbStPf.word_eval (one_mem_UH G) (mul_mem_UH₂ G) hπ.2.1 hexp l hl (zero_mem_lieG G)
  set W : Fin (l.length + 1 + d) → Matrix (Fin n) (Fin n) ℂ := Fin.append Z Y with hWdef
  have hW : ∀ i, W i ∈ lieG G := fun i =>
    Fin.addCases (fun a => by simpa [W, Fin.append_left] using hZ a) (fun b => by simpa [W, Fin.append_right] using hY b) i
  have hG : ContDiff ℝ ∞ (OrbStPf.orb π W w 0) := OrbStPf.contDiff_orb W hW hw 0
  have key : ∀ t, dL π l (π (oneProd Y t) w) =
      OrbStPf.pds (L.map (Fin.castAdd d)) (OrbStPf.orb π W w 0) (Fin.append 0 t) := by
    intro t
    have hv := (smooth_oneProd hπ hw Y hY t)
    have h0 := hval _ hv.1 0
    simp only [zero_smul, NormedSpace.exp_zero, hπ.1, ContinuousLinearMap.one_apply] at h0
    have e : OrbStPf.orb π Z (π (oneProd Y t) w) 0 = fun r => OrbStPf.orb π W w 0 (Fin.append r t) := by
      funext r
      have hA : (List.ofFn fun i => NormedSpace.exp (r i • Z i)).prod ∈ Formalism.QuantumDeterminants.UH G :=
        OrbStPf.list_prod_mem (one_mem_UH G) (mul_mem_UH₂ G) _ (fun a ha => by
          obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha; exact hexp _ (hZ _) _)
      simp only [OrbStPf.orb, List.drop_zero]
      rw [List.ofFn_add (m := d), List.prod_append]
      have e1 : ∀ i : Fin (l.length + 1), Fin.append r t (Fin.castLE (Nat.le_add_right _ d) i) = r i :=
        fun i => Fin.append_left r t i
      have e2 : ∀ i : Fin (l.length + 1), Fin.append Z Y (Fin.castLE (Nat.le_add_right _ d) i) = Z i :=
        fun i => Fin.append_left Z Y i
      simp only [W, e1, e2, Fin.append_right]
      rw [show (List.ofFn fun j : Fin d => NormedSpace.exp (t j • Y j)).prod = oneProd Y t from rfl,
        hπ.2.1 _ hA _ hv.2]
      rfl
    unfold dL
    rw [h0, e, pds_append L _ hG t]
  rw [show (fun t => dL π l (π (oneProd Y t) w)) =
      fun t => OrbStPf.pds (L.map (Fin.castAdd d)) (OrbStPf.orb π W w 0) (Fin.append 0 t) from funext key]
  exact (OrbStPf.contDiff_pds _ hG).continuous.comp (continuous_append_right 0)

attribute [local instance] Formalism.BasicNotions.Host.cmStar in
theorem sobRepM_holds (D : D7) : SobRepM D := by
  intro S Ss M τ
  have hds := M.ds τ
  have hfr := M.fr_unit τ
  have hconj : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D S τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) := fun g hg =>
    OrbStPf.conj_mem _ _ _ _ hfr (M.fr_gram τ) hg
  refine ⟨hds.1, OrbStPf.rep_one M τ, fun a ha b hb => OrbStPf.rep_mul M τ a b ha hb,
    fun g hg v => hds.2.2.1.2.1 _ (hconj g hg) v, fun v => ?_⟩
  have hc : Continuous fun g : Matrix (Fin S.rank) (Fin S.rank) ℂ => M.fr τ * g * (M.fr τ)⁻¹ :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  exact (hds.2.2.1.2.2 v).comp hc.continuousOn (fun g hg => hconj g hg)

end Formalism.IndefR.Tow.SobPf

end
end
