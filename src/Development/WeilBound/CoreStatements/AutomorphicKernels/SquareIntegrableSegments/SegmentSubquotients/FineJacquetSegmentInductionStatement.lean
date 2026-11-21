import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentTermInjectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityCuspidalProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicitySubquotientLeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientCuspidalPermutationStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentSubquotients.ExistsSegmentRepresentationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepSplitIntertwinerStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrictAntiOfTwoExceptionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicitySubquotientLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SocleOfMultiplicityOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientJacquetSegmentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EquivOfMultiplicityOneUniqueFactorStatement

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.LkShuffle2

section Ext

variable {r c : ℕ} {M : Fin c → Type}

open Classical in

def extFam (ι : Fin r → Fin c) (x : ∀ i, M (ι i)) (z : ∀ j, M j) : ∀ j, M j :=
  fun j => if h : ∃ i, ι i = j then h.choose_spec ▸ x h.choose else z j

theorem extFam_apply {ι : Fin r → Fin c} (hι : Function.Injective ι) (x : ∀ i, M (ι i)) (z : ∀ j, M j) (i : Fin r) :
    extFam ι x z (ι i) = x i := by
  have key : ∀ (i' : Fin r) (e : ι i' = ι i), (e ▸ x i' : M (ι i)) = x i := by
    intro i' e
    obtain rfl := hι e
    rfl
  have h : ∃ i', ι i' = ι i := ⟨i, rfl⟩
  unfold extFam
  rw [dif_pos h]
  exact key _ _

theorem extFam_of_not {ι : Fin r → Fin c} (x : ∀ i, M (ι i)) (z : ∀ j, M j) {j : Fin c} (h : ¬ ∃ i, ι i = j) :
    extFam ι x z j = z j := by
  unfold extFam
  rw [dif_neg h]

theorem extFam_update {ι : Fin r → Fin c} (hι : Function.Injective ι) [DecidableEq (Fin r)]
    (x : ∀ i, M (ι i)) (z : ∀ j, M j) (i : Fin r) (v : M (ι i)) :
    extFam ι (Function.update x i v) z = Function.update (extFam ι x z) (ι i) v := by
  funext j
  by_cases h : ∃ i', ι i' = j
  · obtain ⟨i', rfl⟩ := h
    rw [extFam_apply hι]
    by_cases hi : i' = i
    · subst hi
      simp
    · rw [Function.update_of_ne hi, Function.update_of_ne (hι.ne hi), extFam_apply hι]
  · have hj : j ≠ ι i := fun e => h ⟨i, e.symm⟩
    rw [extFam_of_not _ _ h, Function.update_of_ne hj, extFam_of_not _ _ h]

end Ext

section Tensor

variable {r c : ℕ} {X : Fin c → Type} [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)]

def dropMul {ι : Fin r → Fin c} (hι : Function.Injective ι) (z : ∀ j, X j) :
    MultilinearMap ℂ (fun i => X (ι i)) (PiTensorProduct ℂ X) where
  toFun x := PiTensorProduct.tprod ℂ (extFam ι x z)
  map_update_add' := by
    intro _ m i x y
    simp only [extFam_update hι, MultilinearMap.map_update_add]
  map_update_smul' := by
    intro _ m i a x
    simp only [extFam_update hι, MultilinearMap.map_update_smul]

theorem tprod_ne_zero {ι : Type} [Fintype ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (v : ∀ i, V i) (hv : ∀ i, v i ≠ 0) : PiTensorProduct.tprod ℂ v ≠ 0 := by
  have hf : ∀ i, ∃ f : Module.Dual ℂ (V i), f (v i) ≠ 0 := fun i => by
    by_contra hc
    exact hv i ((Module.forall_dual_apply_eq_zero_iff ℂ (v i)).1
      fun f => not_not.1 (not_exists.1 hc f))
  choose f hf using hf
  let F : MultilinearMap ℂ V ℂ := (MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap f
  have hF : PiTensorProduct.lift F (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    rw [PiTensorProduct.lift.tprod]
    simpa [F] using Finset.prod_ne_zero_iff.2 fun i _ => hf i
  intro h
  rw [h, map_zero] at hF
  exact hF rfl

end Tensor

section Sums

variable {r c : ℕ}

theorem sum_castLE_eq (f : Fin c → ℕ) (t : Fin c) :
    ∑ a : Fin (t : ℕ), f (Fin.castLE t.2.le a) = ∑ j, if j < t then f j else 0 := by
  refine Fintype.sum_of_injective (Fin.castLE t.2.le) (Fin.castLE_injective _) _ _ ?_ ?_
  · intro j hj
    rw [if_neg]
    intro hlt
    exact hj ⟨⟨j, hlt⟩, rfl⟩
  · intro a
    rw [if_pos]
    exact a.2

theorem sum_partial (ι : Fin r ↪o Fin c) (b : Fin c → ℕ) (hz : ∀ j, (¬ ∃ i, ι i = j) → b j = 0) (i : Fin r) :
    ∑ a : Fin (ι i : ℕ), b (Fin.castLE (ι i).2.le a) = ∑ a : Fin (i : ℕ), b (ι (Fin.castLE i.2.le a)) := by
  rw [sum_castLE_eq b (ι i), sum_castLE_eq (fun a => b (ι a)) i]
  symm
  refine Fintype.sum_of_injective ι ι.injective _ _ ?_ ?_
  · intro j hj
    rw [hz j (by simpa using hj)]
    simp
  · intro a
    simp

end Sums

section Jac

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r c N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def restrictHom (b : Fin c → ℕ) (ι : Fin r → Fin c) :
    Levi k (fun j => Fin (b j)) →* Levi k (fun i => Fin (b (ι i))) where
  toFun G i := G (ι i)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem eq_one_of_zero {n : ℕ} (h : n = 0) (g : GL (Fin n) k) : g = 1 := by
  subst h
  exact Subsingleton.elim _ _

variable (ι : Fin r ↪o Fin c) (b : Fin c → ℕ) (hb : ∑ j, b j = N) (hb' : ∑ i, b (ι i) = N)
  (hz : ∀ j, (¬ ∃ i, ι i = j) → b j = 0)

include hz in
theorem stdBlocks_drop (i : Fin r) (x : Fin (b (ι i))) :
    stdBlocks b hb ⟨ι i, x⟩ = stdBlocks (fun i => b (ι i)) hb' ⟨i, x⟩ := by
  apply Fin.ext
  rw [stdBlocks_val, stdBlocks_val, sum_partial ι b hz]

include hz in
theorem exists_index {j : Fin c} (x : Fin (b j)) : ∃ i, ι i = j := by
  by_contra h
  have := hz j h
  have := x.2
  omega

include hz in
theorem leviEmb_drop (G : Levi k fun j => Fin (b j)) :
    leviEmb k (stdBlocks b hb) G = leviEmb k (stdBlocks (fun i => b (ι i)) hb') (restrictHom b ι G) := by
  have hE := stdBlocks_drop ι b hb hb' hz
  apply Units.ext
  ext p q
  obtain ⟨⟨a, x⟩, rfl⟩ := (stdBlocks (fun i => b (ι i)) hb').surjective p
  obtain ⟨⟨a', x'⟩, rfl⟩ := (stdBlocks (fun i => b (ι i)) hb').surjective q
  by_cases h : a = a'
  · subst h
    have h1 := leviEmb_apply_same k (stdBlocks b hb) G (ι a) x x'
    rw [hE, hE] at h1
    rw [h1, leviEmb_apply_same]
    rfl
  · have h1 := leviEmb_apply_ne k (stdBlocks b hb) G (ι.injective.ne h) x x'
    rw [hE, hE] at h1
    rw [h1, leviEmb_apply_ne k _ _ h]

include hz in
theorem parab_drop : parab k (stdBlocks b hb) = parab k (stdBlocks (fun i => b (ι i)) hb') := by
  have hE := stdBlocks_drop ι b hb hb' hz
  ext g
  rw [mem_parab_iff, mem_parab_iff]
  constructor
  · intro h a a' x x' hlt
    rw [← hE, ← hE]
    exact h _ _ x x' (ι.lt_iff_lt.2 hlt)
  · intro h a a' x x' hlt
    obtain ⟨a, rfl⟩ := exists_index ι b hz x
    obtain ⟨a', rfl⟩ := exists_index ι b hz x'
    rw [hE, hE]
    exact h _ _ x x' (ι.lt_iff_lt.1 hlt)

include hz in
theorem unipRad_drop : unipRad k (stdBlocks b hb) = unipRad k (stdBlocks (fun i => b (ι i)) hb') := by
  have hE := stdBlocks_drop ι b hb hb' hz
  ext g
  rw [mem_unipRad, mem_unipRad, parab_drop ι b hb hb' hz]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h a x x'
    rw [← hE, ← hE]
    exact h _ x x'
  · intro h a x x'
    obtain ⟨a, rfl⟩ := exists_index ι b hz x
    rw [hE, hE]
    exact h _ x x'

include hz in
theorem modExp_drop (i : Fin r) : modExp (fun i => Fin (b (ι i))) i = modExp (fun j => Fin (b j)) (ι i) := by
  have key : ∀ P : Fin c → Prop, ∀ [DecidablePred P],
      ∑ j with P j, (Fintype.card (Fin (b j)) : ℤ) = ∑ a with P (ι a), (Fintype.card (Fin (b (ι a))) : ℤ) := by
    intro P _
    rw [Finset.sum_filter, Finset.sum_filter]
    symm
    refine Fintype.sum_of_injective ι ι.injective _ _ ?_ fun a => rfl
    intro j hj
    rw [hz j (by simpa using hj)]
    simp
  unfold modExp
  rw [key, key]
  simp only [ι.lt_iff_lt]

include hz in
theorem deltaHalf_drop (G : Levi k fun j => Fin (b j)) :
    deltaHalf k (fun j => Fin (b j)) G = deltaHalf k (fun i => Fin (b (ι i))) (restrictHom b ι G) := by
  rw [deltaHalf_apply, deltaHalf_apply]
  symm
  refine Fintype.prod_of_injective ι ι.injective _ _ ?_ ?_
  · intro j hj
    rw [eq_one_of_zero (hz j (by simpa using hj)) (G j)]
    simp
  · intro a
    rw [modExp_drop ι b hz]
    rfl

include hz in

theorem nonempty_jac_equiv (π : Representation ℂ (GL (Fin N) k) V) :
    Nonempty ((jac (stdBlocks b hb) π).Equiv
      ((jac (stdBlocks (fun i => b (ι i)) hb') π).comp (restrictHom b ι))) := by
  have hU := unipRad_drop (k := k) ι b hb hb' hz
  refine ⟨.mk (Submodule.quotEquivOfEq _ _ (congrArg (fun U => twKer π U 1) hU)) fun g => ?_⟩
  refine LinearMap.ext fun y => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have h1 : leviEmb k (stdBlocks b hb) g = leviEmb k (stdBlocks (fun i => b (ι i)) hb') (restrictHom b ι g) :=
    leviEmb_drop ι b hb hb' hz g
  have h2 := deltaHalf_drop (k := k) ι b hz g
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, MonoidHom.comp_apply]
  rw [jac_mk, map_smul, Submodule.quotEquivOfEq_mk, Submodule.quotEquivOfEq_mk, jac_mk, h1, h2]

end Jac

section Abstract

variable {G G' V W : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem injective_of_comp (ψ : G' →* G) (hψ : Function.Surjective ψ) {ρ : Representation ℂ G V}
    (hρ : ρ.IsIrreducible) {σ : Representation ℂ G' W}
    (f : Representation.IntertwiningMap (ρ.comp ψ : Representation ℂ G' V) σ) {v : V} (hv : f v ≠ 0) : Function.Injective f := by
  let S : Subrepresentation ρ := ⟨LinearMap.ker f.toLinearMap, fun g w hw => by
    obtain ⟨g', rfl⟩ := hψ g
    have h1 : f w = 0 := hw
    have h2 := f.isIntertwining _ _ g' w
    show f (ρ (ψ g') w) = 0
    have h3 : f (ρ (ψ g') w) = σ g' (f w) := h2
    rw [h3, h1, map_zero]⟩
  rcases eq_bot_or_eq_top S with h | h
  · refine (injective_iff_map_eq_zero f).2 fun w hw => ?_
    have h1 : w ∈ S.toSubmodule := hw
    rw [h] at h1
    exact h1
  · have h1 : v ∈ S.toSubmodule := by rw [h]; trivial
    exact absurd h1 hv

theorem exists_common {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (f : ρ.IntertwiningMap σ) {v : V}
    (hv : f v ≠ 0) : ∃ (Z : Type) (_ : AddCommGroup Z) (_ : Module ℂ Z) (υ : Representation ℂ G Z),
      υ.IsIrreducible ∧ IsSubquotient υ ρ ∧ IsSubquotient υ σ := by
  let S : Subrepresentation σ := ⟨LinearMap.range f.toLinearMap, by
    rintro g _ ⟨w, rfl⟩
    exact ⟨ρ g w, f.isIntertwining _ _ g w⟩⟩
  haveI : Nontrivial S.toSubmodule := ⟨⟨⟨f v, v, rfl⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩
  obtain ⟨Z, i1, i2, υ, hυ, hs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _ S.toRepresentation inferInstance
  let q : ρ.IntertwiningMap S.toRepresentation :=
    ⟨LinearMap.codRestrict S.toSubmodule f.toLinearMap fun w => ⟨w, rfl⟩, fun g => LinearMap.ext fun w =>
      Subtype.ext (f.isIntertwining _ _ g w)⟩
  let ι : S.toRepresentation.IntertwiningMap σ := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  refine ⟨Z, i1, i2, υ, hυ, hs.trans (.of_surjective q ?_), hs.trans (.of_injective ι Subtype.val_injective)⟩
  rintro ⟨_, w, rfl⟩
  exact ⟨w, rfl⟩

end Abstract

section Rep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r c N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem isSubquotient_jac_drop (ι : Fin r ↪o Fin c) (b : Fin c → ℕ) (hb : ∑ j, b j = N) (hb' : ∑ i, b (ι i) = N)
    (hz : ∀ j, (¬ ∃ i, ι i = j) → b j = 0) (π : Representation ℂ (GL (Fin N) k) V)
    (s : ∀ j, IrrRep (GL (Fin (b j)) k)) (hI : (piTensor fun i => (s (ι i)).ρ).IsIrreducible)
    (h : IsSubquotient (piTensor fun j => (s j).ρ) (jac (stdBlocks b hb) π)) :
    IsSubquotient (piTensor fun i => (s (ι i)).ρ) (jac (stdBlocks (fun i => b (ι i)) hb') π) := by
  classical
  obtain ⟨φ⟩ := nonempty_jac_equiv (k := k) ι b hb hb' hz π
  have hv : ∀ j, ∃ v : (s j).V, v ≠ 0 := fun j => by
    haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible (s j).irr
    exact exists_ne 0
  choose z hzne using hv
  have hsurj : Function.Surjective (restrictHom (k := k) b ι) := fun g =>
    ⟨extFam (M := fun j => GL (Fin (b j)) k) ι g fun _ => 1, funext fun i => extFam_apply (M := fun j => GL (Fin (b j)) k) ι.injective g (fun _ => 1) i⟩
  let L := PiTensorProduct.lift (dropMul (X := fun j => (s j).V) ι.injective z)
  have hL : ∀ x, L (PiTensorProduct.tprod ℂ x) = PiTensorProduct.tprod ℂ (extFam ι x z) := fun x => by
    simp only [L, PiTensorProduct.lift.tprod]
    rfl
  let F : Representation.IntertwiningMap
      ((piTensor fun i => (s (ι i)).ρ).comp (restrictHom (k := k) b ι)) (piTensor fun j => (s j).ρ) :=
    ⟨L, fun G => PiTensorProduct.ext (MultilinearMap.ext fun x => by
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, MonoidHom.comp_apply, piTensor_tprod, hL]
      congr 1
      funext j
      by_cases hj : ∃ i, ι i = j
      · obtain ⟨i, rfl⟩ := hj
        rw [extFam_apply ι.injective, extFam_apply ι.injective]
        rfl
      · rw [extFam_of_not _ _ hj, extFam_of_not _ _ hj, eq_one_of_zero (hz j hj) (G j), map_one]
        rfl)⟩
  have hne : ∀ i, (fun i => z (ι i)) i ≠ 0 := fun i => hzne _
  have hF : F (PiTensorProduct.tprod ℂ fun i => z (ι i)) ≠ 0 := by
    show L _ ≠ 0
    rw [hL]
    refine tprod_ne_zero _ fun j => ?_
    by_cases hj : ∃ i, ι i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [extFam_apply ι.injective]
      exact hzne _
    · rw [extFam_of_not _ _ hj]
      exact hzne _
  have hinj := injective_of_comp (restrictHom (k := k) b ι) hsurj hI F hF
  exact GlobalTheory.JacStages.isSubquotient_of_comp (restrictHom (k := k) b ι) hsurj
    ((IsSubquotient.of_injective F hinj).trans (h.trans (GlobalTheory.JacStages.isSubquotient_of_equiv φ)))

theorem of_eq_of_jac (D₁ D₂ : Fin r → ℕ) (hD : D₁ = D₂) (h₁ : ∑ i, D₁ i = N) (h₂ : ∑ i, D₂ i = N)
    (π : Representation ℂ (GL (Fin N) k) V) (σ₁ : ∀ i, IrrRep (GL (Fin (D₁ i)) k))
    (σ₂ : ∀ i, IrrRep (GL (Fin (D₂ i)) k))
    (hsub : IsSubquotient (piTensor fun i => (σ₁ i).ρ) (jac (stdBlocks D₁ h₁) π))
    (φ : (jac (stdBlocks D₂ h₂) π).Equiv (piTensor fun i => (σ₂ i).ρ)) (i : Fin r) :
    IrrGL.of (σ₁ i).ρ (σ₁ i).smooth (σ₁ i).irr = IrrGL.of (σ₂ i).ρ (σ₂ i).smooth (σ₂ i).irr := by
  subst hD
  have h1 := hsub.trans (GlobalTheory.JacStages.isSubquotient_of_equiv φ)
  have h2 := (GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle (fun i => (σ₁ i).ρ) (fun i => (σ₁ i).irr) i).trans
    (SupportUnique.isSubquotient_comp h1 (MonoidHom.mulSingle (fun i => GL (Fin (D₁ i)) k) i))
  have h3 := SupportUnique.isSubquotient_factor (fun i => (σ₂ i).ρ) i (σ₁ i).irr h2
  obtain ⟨ψ⟩ := SupportUnique.nonempty_equiv_of_isSubquotient (σ₁ i).irr (σ₂ i).irr h3
  exact IrrGL.of_eq_of.2 ⟨ψ.symm⟩

theorem exists_col {x : IrrGL k} (hx : x.IsCusp) {h : ℕ} {c : Fin h → ℕ} (e : (Σ i, Fin (c i)) ≃ Fin x.1)
    (s : ∀ i, IrrRep (GL (Fin (c i)) k)) (hsub : IsSubquotient x.rep (multiProd e fun i => (s i).ρ)) :
    ∃ a, (∀ i, i ≠ a → c i = 0) ∧ IrrGL.of (s a).ρ (s a).smooth (s a).irr = x := by
  obtain ⟨ι, hι⟩ := SupportUnique.exists_map_of_isCuspidal hx.1 x.2.rep.irr hx.2 (isSmooth_parInd _ _)
    (SupportUnique.exists_scalar_multiProd e (fun a => (s a).ρ) (fun a => (s a).smooth) fun a => (s a).irr) hsub
  have hne : GlobalTheory.SmGL.Model.evalOne e ι ≠ 0 := by
    intro h0
    refine hι ((GlobalTheory.SmGL.Model.evalOne_bijective e hx.2.1 _).1 ?_)
    refine h0.trans ?_
    refine Representation.IntertwiningMap.ext (LinearMap.ext fun v => ?_)
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    rfl
  have hU : unipRad k e = ⊥ := by
    by_contra hU
    haveI := hx.2.2 h _ e hU
    refine hne (Representation.IntertwiningMap.ext (LinearMap.ext fun v => ?_))
    rw [Subsingleton.elim v 0, map_zero]
    rfl
  obtain ⟨⟨a, i⟩, -⟩ := e.surjective ⟨0, hx.1⟩
  have ha : ∀ j, j ≠ a → c j = 0 := by
    intro j hj
    by_contra hj0
    refine GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.2 ?_ hU
    rcases lt_or_gt_of_ne hj with h | h
    · exact ⟨e ⟨j, ⟨0, by omega⟩⟩, e ⟨a, i⟩, by rwa [blk_apply, blk_apply]⟩
    · exact ⟨e ⟨a, i⟩, e ⟨j, ⟨0, by omega⟩⟩, by rwa [blk_apply, blk_apply]⟩
  refine ⟨a, ha, ?_⟩
  obtain ⟨d, y⟩ := x
  obtain rfl : c a = d := by
    have h1 : ∑ j, c j = d := by simpa using Fintype.card_congr e
    rwa [Finset.sum_eq_single a (fun j _ hj => ha j hj) (by simp)] at h1
  obtain ⟨v, hv⟩ : ∃ v, GlobalTheory.SmGL.Model.evalOne e ι v ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hne (Representation.IntertwiningMap.ext (LinearMap.ext hc))
  let ψ := compMap (GlobalTheory.SmGL.Model.evalOne e ι) (MonoidHom.mulSingle (fun j => GL (Fin (c j)) k) a)
  obtain ⟨Z, _, _, υ, hυ, h1, h2⟩ := exists_common ψ (v := v) hv
  obtain ⟨φ₁⟩ := SupportUnique.nonempty_equiv_of_isSubquotient hυ y.rep.irr
    (h1.trans (SupportUnique.isSubquotient_jac_single a ha e _))
  obtain ⟨φ₂⟩ := SupportUnique.nonempty_equiv_of_isSubquotient hυ (s a).irr
    (SupportUnique.isSubquotient_factor _ a hυ h2)
  exact (IrrGL.of_eq_of.2 ⟨φ₂.trans φ₁.symm⟩).trans (IrrGL.of_rep ⟨_, y⟩)

end Rep

section Main

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_cell_data (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h c N : ℕ} (x : Fin h → IrrGL k)
    (hd : ∑ i, (x i).1 = N) (y : Fin c → IrrGL k) (hy : ∑ i, (y i).1 = N) (hyc : ∀ i, (y i).IsCusp)
    (hjm : 1 ≤ jm y hy (prodIrr x hd)) :
    ∃ (b : Fin h → Fin c → ℕ) (hb : ∀ i, ∑ j, b i j = (x i).1) (s : ∀ i j, IrrRep (GL (Fin (b i j)) k)),
      (∀ i, IsSubquotient (piTensor fun j => (s i j).ρ) (jac (stdBlocks (b i) (hb i)) (x i).rep)) ∧
      ∀ j, ∃ a, (∀ i, i ≠ a → b i j = 0) ∧ IrrGL.of (s a j).ρ (s a j).smooth (s a j).irr = y j := by
  classical
  have hτ := GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor hA y
  have hτs : IsSmooth (piTensor fun j => (y j).rep) := isSmooth_piTensor fun j => (y j).2.rep.smooth
  obtain ⟨hG, hC⟩ := GlobalTheory.CompanionTheory.GeoLink.geometricLemma k
  let M : Fin h → Type := fun i => Fin (x i).1
  let M' : Fin c → Type := fun j => Fin (y j).1
  haveI : Fintype (SizeMatrix M M') := Fintype.ofFinite _
  have hr : ∀ (b : SizeMatrix M M') i, ∑ j, b.1 i j = (x i).1 := fun b i => by simpa [M] using b.2.1 i
  let fR : ∀ (b : SizeMatrix M M') i, (Σ j, Fin (b.1 i j)) ≃ M i := fun b i => stdBlocks (b.1 i) (hr b i)
  let gC : ∀ (b : SizeMatrix M M') j, (Σ i, Fin (b.1 i j)) ≃ M' j := fun b => b.nonempty_cols.some
  have h0 : jhMult (piTensor fun j => (y j).rep) (jac (stdBlocks (fun j => (y j).1) hy) (prodIrr x hd)) ≠ 0 :=
    ENat.one_le_iff_ne_zero.1 hjm
  have h1 := hG.jhMult_eq (m := M) (m' := M') (stdBlocks (fun i => (x i).1) hd) (stdBlocks (fun j => (y j).1) hy)
    (isSmooth_piTensor fun i => (x i).2.rep.smooth) fR gC hτ
  have h2 : ∑ b, jhMult (piTensor fun j => (y j).rep)
      (cellFunctor (fR b) (gC b) (piTensor fun i => (x i).rep)) ≠ 0 := fun e => h0 (h1.trans e)
  obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero h2
  obtain ⟨T, -, hT⟩ := hC _ _ M M' _ (fR b) (gC b) _ (fun i => (x i).rep) (fun i => (x i).2.rep.smooth)
    (fun i => hasFiniteLength_of_isIrreducible (x i).2.rep.irr)
  rw [hT ⟨_, piTensor fun j => (y j).rep, hτs, hτ⟩] at hb
  obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  have hcol : IsSubquotient (piTensor fun j => (y j).rep)
      (piTensor fun j => multiProd (gC b j) fun i => (s i j).rep.ρ) := jhMult_ne_zero_iff.1 (right_ne_zero_of_mul hs)
  refine ⟨b.1, hr b, fun i j => (s i j).rep, fun i => jhMult_ne_zero_iff.1
    (Finset.prod_ne_zero_iff.1 (left_ne_zero_of_mul hs) i (Finset.mem_univ i)), fun j => ?_⟩
  have h3 := (GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle (fun j => (y j).rep) (fun j => (y j).2.rep.irr) j).trans
    (SupportUnique.isSubquotient_comp hcol (MonoidHom.mulSingle (fun j => GL (Fin (y j).1) k) j))
  exact exists_col (hyc j) (gC b j) _
    (SupportUnique.isSubquotient_factor (fun j => multiProd (gC b j) fun i => (s i j).rep.ρ) j (y j).2.rep.irr h3)

theorem exists_row (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {p c : ℕ} (x : IrrGL k) (s : Fin p → IrrGL k)
    (hs : ∑ i, (s i).1 = x.1) (d : ℕ) (hsd : ∀ i, (s i).1 = d) (hsc : ∀ i, (s i).IsCusp)
    (hu : Nonempty ((jac (stdBlocks (fun i => (s i).1) hs) x.rep).Equiv (piTensor fun i => (s i).rep)))
    (b : Fin c → ℕ) (hb : ∑ j, b j = x.1) (w : ∀ j, IrrRep (GL (Fin (b j)) k))
    (hsub : IsSubquotient (piTensor fun j => (w j).ρ) (jac (stdBlocks b hb) x.rep))
    (y : Fin c → IrrGL k) (hyc : ∀ j, (y j).IsCusp)
    (hw : ∀ j, b j ≠ 0 → IrrGL.of (w j).ρ (w j).smooth (w j).irr = y j) :
    ∃ f : Fin p ↪o Fin c, (∀ i, b (f i) ≠ 0) ∧ ∀ i, y (f i) = s i := by
  classical
  obtain ⟨r, ι, hz, hpos⟩ : ∃ (r : ℕ) (ι : Fin r ↪o Fin c), (∀ j, (¬ ∃ i, ι i = j) → b j = 0) ∧
      ∀ i, b (ι i) ≠ 0 := by
    let A : Finset (Fin c) := Finset.univ.filter fun j => b j ≠ 0
    refine ⟨A.card, A.orderEmbOfFin rfl, fun j hj => ?_, fun i => ?_⟩
    · by_contra h0
      have hm : j ∈ (A : Set (Fin c)) := by simpa [A] using h0
      rw [← Finset.range_orderEmbOfFin A rfl] at hm
      exact hj hm
    · exact (Finset.mem_filter.1 (A.orderEmbOfFin_mem rfl i)).2
  have hb' : ∑ i, b (ι i) = x.1 := by
    rw [← hb]
    exact Fintype.sum_of_injective ι ι.injective _ _ (fun j hj => hz j (by simpa using hj)) fun _ => rfl
  let y' : Fin r → IrrGL k := fun i => IrrGL.of (w (ι i)).ρ (w (ι i)).smooth (w (ι i)).irr
  have hyy : ∀ i, y' i = y (ι i) := fun i => hw _ (hpos i)
  have hy'c : ∀ i, (y' i).IsCusp := fun i => by rw [hyy]; exact hyc _
  let φ : (piTensor fun i => (w (ι i)).ρ).Equiv (piTensor fun i => (y' i).rep) :=
    piTensorEquiv fun i => IrrGL.equivOf (w (ι i)).ρ (w (ι i)).smooth (w (ι i)).irr
  have hI : (piTensor fun i => (w (ι i)).ρ).IsIrreducible :=
    GlobalTheory.Parabolic.isIrreducible_of_equiv φ.symm (GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor hA y')
  have hdrop := isSubquotient_jac_drop ι b hb hb' hz x.rep w hI hsub
  have hsum : ∑ i, (y' i).1 = x.1 := hb'
  have hjm : 1 ≤ jm y' hsum x.rep := ENat.one_le_iff_ne_zero.2 (jhMult_ne_zero_iff.2
    ((GlobalTheory.JacStages.isSubquotient_of_equiv φ.symm).trans hdrop))
  obtain ⟨ψ⟩ := hu
  haveI := GlobalTheory.ProdSupport.nontrivial_piTensor (fun a => (s a).2.rep.V)
    fun a => GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible (s a).2.rep.irr
  obtain ⟨t, ht⟩ := exists_ne (0 : PiTensorProduct ℂ fun a => (s a).2.rep.V)
  obtain ⟨F, hF⟩ := (GlobalTheory.SmGL.Model.evalOne_bijective (stdBlocks (fun i => (s i).1) hs) x.2.rep.smooth _).2
    ψ.toIntertwiningMap
  have hQ : IsSubquotient x.rep (prodIrr s hs) := by
    obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (ψ.symm t)
    have h1 : GlobalTheory.SmGL.Model.evalOne _ F (Submodule.Quotient.mk v) = t := by
      rw [hF, hv]
      exact ψ.apply_symm_apply t
    have h2 : F v ≠ 0 := by
      intro h0
      refine ht (h1.symm.trans ?_)
      show (F v).1.1 1 = 0
      rw [h0]
      rfl
    exact .of_injective F (injective_of_comp (MonoidHom.id _) Function.surjective_id x.2.rep.irr F h2)
  have hP : 1 ≤ jm y' hsum (prodIrr s hs) :=
    hjm.trans (GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient y' hsum x.rep (prodIrr s hs) (isSmooth_prodIrr _ _) hQ)
  rw [GlobalTheory.T.jacquet_multiplicity_cuspidal_product hA s y' hs hsum hsc hy'c] at hP
  obtain ⟨e, he⟩ : ∃ e : Fin r ≃ Fin p, ∀ a, y' a = s (e a) := by
    by_contra hc
    have h0 : {e : Fin r ≃ Fin p | ∀ a, y' a = s (e a)} = ∅ := Set.eq_empty_of_forall_notMem fun e he => hc ⟨e, he⟩
    rw [h0] at hP
    simp at hP
  obtain rfl : r = p := by simpa using Fintype.card_congr e
  have hdeg : (fun i => b (ι i)) = fun i => (s i).1 := funext fun i => by
    have h1 : (y' i).1 = (s (e i)).1 := congrArg Sigma.fst (he i)
    exact h1.trans ((hsd _).trans (hsd i).symm)
  refine ⟨ι, hpos, fun i => ?_⟩
  have h2 := of_eq_of_jac (fun i => b (ι i)) (fun i => (s i).1) hdeg hb' hs x.rep (fun i => w (ι i))
    (fun i => (s i).2.rep) hdrop ψ i
  exact (hyy i).symm.trans (h2.trans (IrrGL.of_rep (s i)))

theorem shuffle2 : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {p q N c : ℕ} (u v : IrrGL k) (s : Fin p → IrrGL k) (t : Fin q → IrrGL k) (hs : ∑ i, (s i).1 = u.1) (ht : ∑ i, (t i).1 = v.1) (d : ℕ) (hsd : ∀ i, (s i).1 = d) (htd : ∀ j, (t j).1 = d) (hsc : ∀ i, (s i).IsCusp) (htc : ∀ i, (t i).IsCusp) (hu : Nonempty ((jac (stdBlocks (fun i => (s i).1) hs) u.rep).Equiv (piTensor fun i => (s i).rep))) (hv : Nonempty ((jac (stdBlocks (fun i => (t i).1) ht) v.rep).Equiv (piTensor fun i => (t i).rep))) (hd : ∑ i, (![u, v] i).1 = N) (y : Fin c → IrrGL k) (hy : ∑ i, (y i).1 = N) (hyc : ∀ i, (y i).IsCusp) (h : 1 ≤ jm y hy (prodIrr ![u, v] hd)), ∃ (f : Fin p ↪o Fin c) (g : Fin q ↪o Fin c), Disjoint (Set.range f) (Set.range g) ∧ (∀ i, y (f i) = s i) ∧ ∀ j, y (g j) = t j := by
  intro k _ _ _ _ hA p q N c u v s t hs ht d hsd htd hsc htc hu hv hd y hy hyc h
  obtain ⟨b, hb, w, hrow, hcol⟩ := exists_cell_data hA ![u, v] hd y hy hyc h
  choose a ha haw using hcol
  have key : ∀ (i : Fin 2) j, b i j ≠ 0 → IrrGL.of (w i j).ρ (w i j).smooth (w i j).irr = y j := by
    intro i j hj
    obtain rfl : a j = i := by_contra fun hne => hj (ha j i (Ne.symm hne))
    exact haw j
  obtain ⟨f, hf, hfs⟩ := exists_row hA u s hs d hsd hsc hu (b 0) (hb 0) (w 0) (hrow 0) y hyc (key 0)
  obtain ⟨g, hg, hgt⟩ := exists_row hA v t ht d htd htc hv (b 1) (hb 1) (w 1) (hrow 1) y hyc (key 1)
  refine ⟨f, g, Set.disjoint_left.2 ?_, hfs, hgt⟩
  rintro _ ⟨i, rfl⟩ ⟨l, hl⟩
  have h0 := hf i
  have h1 := hg l
  rw [hl] at h1
  by_cases e : a (f i) = 0
  · exact h1 (ha _ 1 (by rw [e]; decide))
  · exact h0 (ha _ 0 (Ne.symm e))

end Main

end GlobalTheory.CompanionTheory.LkShuffle2
end
end

section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
theorem _root_.GlobalTheory.TL.derivative_cuspidal_pair_length : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {p q N c : ℕ} (u v : IrrGL k) (s : Fin p → IrrGL k) (t : Fin q → IrrGL k) (hs : ∑ i, (s i).1 = u.1) (ht : ∑ i, (t i).1 = v.1) (d : ℕ) (hsd : ∀ i, (s i).1 = d) (htd : ∀ j, (t j).1 = d) (hsc : ∀ i, (s i).IsCusp) (htc : ∀ i, (t i).IsCusp) (hu : Nonempty ((jac (stdBlocks (fun i => (s i).1) hs) u.rep).Equiv (piTensor fun i => (s i).rep))) (hv : Nonempty ((jac (stdBlocks (fun i => (t i).1) ht) v.rep).Equiv (piTensor fun i => (t i).rep))) (hd : ∑ i, (![u, v] i).1 = N) (y : Fin c → IrrGL k) (hy : ∑ i, (y i).1 = N) (hyc : ∀ i, (y i).IsCusp) (h : 1 ≤ jm y hy (prodIrr ![u, v] hd)), ∃ (f : Fin p ↪o Fin c) (g : Fin q ↪o Fin c), Disjoint (Set.range f) (Set.range g) ∧ (∀ i, y (f i) = s i) ∧ ∀ j, y (g j) = t j := by
  first | exact @GlobalTheory.CompanionTheory.LkShuffle2.shuffle2 | exact GlobalTheory.CompanionTheory.LkShuffle2.shuffle2
end

section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

noncomputable section

namespace GlobalTheory.CompanionTheory.LkSegFine

theorem cover {p q c d : ℕ} (deg : Fin c → ℕ) (hpos : ∀ a, 0 < deg a) (hsum : ∑ a, deg a = (p + q) * d)
    (f : Fin p → Fin c) (g : Fin q → Fin c) (hf : Function.Injective f) (hg : Function.Injective g)
    (hdis : Disjoint (Set.range f) (Set.range g)) (hfd : ∀ i, deg (f i) = d) (hgd : ∀ j, deg (g j) = d) :
    (∀ a, a ∈ Set.range f ∨ a ∈ Set.range g) ∧ c = p + q := by
  let φ : Fin p ⊕ Fin q → Fin c := Sum.elim f g
  have hφ : Function.Injective φ := by
    rintro (x | x) (z | z) h
    · exact congrArg _ (hf h)
    · exact absurd (show g z ∈ Set.range f from ⟨x, h⟩) (Set.disjoint_left.1 hdis · ⟨z, rfl⟩)
    · exact absurd (show f z ∈ Set.range g from ⟨x, h⟩) (Set.disjoint_right.1 hdis · ⟨z, rfl⟩)
    · exact congrArg _ (hg h)
  have hS : ∑ x : Fin p ⊕ Fin q, deg (φ x) = (p + q) * d := by
    simp [Fintype.sum_sum_type, φ, hfd, hgd, add_mul]
  have hsurj : Function.Surjective φ := by
    intro a
    by_contra hne
    have h2 : ∑ b ∈ Finset.univ.image φ, deg b = (p + q) * d := by
      rw [Finset.sum_image hφ.injOn]; exact hS
    have h3 : a ∉ Finset.univ.image φ := by
      simpa using fun x h => hne ⟨x, h⟩
    have h4 : deg a + ∑ b ∈ Finset.univ.image φ, deg b ≤ ∑ b, deg b := by
      rw [← Finset.sum_insert h3]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have := hpos a
    omega
  refine ⟨fun a => ?_, ?_⟩
  · obtain ⟨x | x, rfl⟩ := hsurj a
    · exact Or.inl ⟨x, rfl⟩
    · exact Or.inr ⟨x, rfl⟩
  · have := Fintype.card_of_bijective (⟨hφ, hsurj⟩ : Function.Bijective φ)
    simpa using this.symm

theorem word_eq_decreasing {X : Type*} (l : ℕ) (hl : 3 ≤ l) (t : ℕ → X)
    (hinj : ∀ a b, a < l → b < l → t a = t b → a = b) (y : Fin l → X)
    (i : Fin l) (g : Fin (l - 1) ↪o Fin l) (hcov : ∀ a, a = i ∨ a ∈ Set.range g) (hi : y i = t 0)
    (hg : ∀ j : Fin (l - 1), y (g j) = t (l - 1 - j))
    (i' : Fin l) (f : Fin (l - 1) ↪o Fin l) (hcov' : ∀ a, a = i' ∨ a ∈ Set.range f) (hi' : y i' = t (l - 1))
    (hf : ∀ j : Fin (l - 1), y (f j) = t (l - 2 - j)) (a : Fin l) : y a = t (l - 1 - a) := by
  have hex : ∀ a, ∃ n, n < l ∧ y a = t n := fun a => by
    rcases hcov a with rfl | ⟨j, rfl⟩
    · exact ⟨0, by omega, hi⟩
    · exact ⟨_, by omega, hg j⟩
  choose w hw hyw using hex
  have hwi : w i = 0 := hinj _ _ (hw i) (by omega) ((hyw i).symm.trans hi)
  have hwi' : w i' = l - 1 := hinj _ _ (hw i') (by omega) ((hyw i').symm.trans hi')
  have hwg : ∀ j, w (g j) = l - 1 - j := fun j => hinj _ _ (hw _) (by omega) ((hyw _).symm.trans (hg j))
  have hwf : ∀ j, w (f j) = l - 2 - j := fun j =>
    hinj _ _ (hw _) (by omega) ((hyw _).symm.trans (hf j))
  have h1 : ∀ a b, a < b → a ≠ i → b ≠ i → w b < w a := by
    intro a b hab ha hb
    obtain ⟨ja, rfl⟩ := (hcov a).resolve_left ha
    obtain ⟨jb, rfl⟩ := (hcov b).resolve_left hb
    have h2 : ja < jb := g.lt_iff_lt.1 hab
    have h3 := Fin.lt_def.1 h2
    have h4 := jb.2
    rw [hwg, hwg]
    omega
  have h2 : ∀ a b, a < b → a ≠ i' → b ≠ i' → w b < w a := by
    intro a b hab ha hb
    obtain ⟨ja, rfl⟩ := (hcov' a).resolve_left ha
    obtain ⟨jb, rfl⟩ := (hcov' b).resolve_left hb
    have h2 : ja < jb := f.lt_iff_lt.1 hab
    have h3 := Fin.lt_def.1 h2
    have h4 := jb.2
    rw [hwf, hwf]
    omega
  have hanti : StrictAnti w := GlobalTheory.T.strict_anti_of_two_exceptions l hl w hw i i' hwi hwi' h1 h2
  let φ : Fin l → Fin l := fun a => Fin.rev ⟨w a, hw a⟩
  have hφ : StrictMono φ := fun a b hab => Fin.rev_lt_rev.2 (Fin.lt_def.2 (hanti hab))
  have h3 : φ a = a := le_antisymm hφ.apply_le hφ.le_apply
  have h4 : l - (w a + 1) = a := by
    have := congrArg Fin.val h3
    simpa [φ, Fin.val_rev] using this
  have h5 := hw a
  have h6 : w a = l - 1 - a := by omega
  rw [hyw a, h6]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sum_dec_fst (Γ : Segment k) : ∑ a, (dec Γ a).1 = Γ.deg := by
  show ∑ _ : Fin Γ.len, Γ.d = _
  simp [Segment.deg]

theorem isCusp_dec (Γ : Segment k) (a : Fin Γ.len) : (dec Γ a).IsCusp := Γ.isCusp_term _

theorem jm_congr {h N : ℕ} {x x' : Fin h → IrrGL k} (e : x = x') (hd : ∑ a, (x a).1 = N) (hd' : ∑ a, (x' a).1 = N)
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) : jm x hd π = jm x' hd' π := by
  subst e
  rfl

theorem dec_segLow (Δ : Segment k) (a : ℕ) (h0 : 0 < a) (i : Fin (segLow Δ a h0).len) :
    dec (segLow Δ a h0) i = Δ.first.nu ((a - 1 - (i : ℕ) : ℕ) : ℂ) := by
  have hi : (i : ℕ) < a := i.2
  have e : ((Fin.rev i : Fin (segLow Δ a h0).len) : ℕ) = a - 1 - i := by
    rw [Fin.val_rev]
    show a - ((i : ℕ) + 1) = _
    omega
  show Δ.first.nu (((Fin.rev i : Fin (segLow Δ a h0).len) : ℕ) : ℂ) = _
  rw [e]

theorem dec_segHigh (Δ : Segment k) (a : ℕ) (h1 : a < Δ.len) (j : Fin (segHigh Δ a h1).len) :
    dec (segHigh Δ a h1) j = Δ.first.nu ((a + (Δ.len - a - 1 - (j : ℕ)) : ℕ) : ℂ) := by
  have hj : (j : ℕ) < Δ.len - a := j.2
  have e : ((Fin.rev j : Fin (segHigh Δ a h1).len) : ℕ) = Δ.len - a - 1 - j := by
    rw [Fin.val_rev]
    show Δ.len - a - ((j : ℕ) + 1) = _
    omega
  show (Δ.first.nu ((a : ℕ) : ℂ)).nu (((Fin.rev j : Fin (segHigh Δ a h1).len) : ℕ) : ℂ) = _
  rw [e, IrrGL.nu_nu]
  push_cast
  rfl

theorem exists_class (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Γ : Segment k) :
    ∃ u : IrrGL k, u.1 = Γ.deg ∧ IsLSeg Γ u.rep := by
  obtain ⟨τ, hd, hc⟩ := GlobalTheory.TL.exists_segment_representation hA Γ
  exact ⟨IrrGL.of τ.ρ τ.smooth τ.irr, rfl, hd, hc.of_equiv (IrrGL.equivOf _ _ _) (Representation.Equiv.refl _)⟩

theorem fine_tensor (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Γ : Segment k) (hF : FineJac Γ) (u : IrrGL k)
    (hu : IsLSeg Γ u.rep) (hs : ∑ i, (dec Γ i).1 = u.1) :
    Nonempty ((jac (stdBlocks (fun i => (dec Γ i).1) hs) u.rep).Equiv (piTensor fun i => (dec Γ i).rep)) := by
  have hJ : HasFiniteLength (jac (stdBlocks (fun i => (dec Γ i).1) hs) u.rep) :=
    GlobalTheory.T.jacquet_module_finite_length k _ _ _ _ _ _ u.2.rep.smooth (hasFiniteLength_of_isIrreducible u.2.rep.irr)
  exact GlobalTheory.T.equiv_of_multiplicity_one_unique_factor _ _ (GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA (dec Γ)) hJ ((hF u.rep hu).1 hs)
    fun X _ _ ρ hi hq => GlobalTheory.T.irreducible_subquotient_jacquet_segment hA Γ hF u hu hs X ρ hi hq

theorem shuffle_step (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hπ : IsLSeg Δ π) (a : ℕ) (h0 : 0 < a) (h1 : a < Δ.len)
    (hlow : FineJac (segLow Δ a h0)) (hhigh : FineJac (segHigh Δ a h1)) {c : ℕ} (y : Fin c → IrrGL k)
    (hy : ∑ i, (y i).1 = N) (hyc : ∀ i, (y i).IsCusp) (h : 1 ≤ jm y hy π) :
    ∃ (f : Fin (segLow Δ a h0).len ↪o Fin c) (g : Fin (segHigh Δ a h1).len ↪o Fin c),
      Disjoint (Set.range f) (Set.range g) ∧ (∀ i, y (f i) = dec (segLow Δ a h0) i) ∧
        ∀ j, y (g j) = dec (segHigh Δ a h1) j := by
  obtain ⟨u, hu1, hu⟩ := exists_class hA (segLow Δ a h0)
  obtain ⟨v, hv1, hv⟩ := exists_class hA (segHigh Δ a h1)
  have hN : N = Δ.len * Δ.d := by
    obtain ⟨hd, -⟩ := hπ
    rw [← hd, Segment.sum_term_fst]
    rfl
  have hd : ∑ i, (![u, v] i).1 = N := by
    have e1 : (segLow Δ a h0).deg = a * Δ.d := rfl
    have e2 : (segHigh Δ a h1).deg = (Δ.len - a) * Δ.d := rfl
    rw [Fin.sum_univ_two]
    show u.1 + v.1 = N
    rw [hu1, hv1, e1, e2, ← Nat.add_mul, Nat.add_sub_cancel' h1.le, hN]
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.segment_rep_split_intertwiner hA Δ π hπ a h0 h1 u v hu hv hd
  have hle := GlobalTheory.T.jacquet_multiplicity_subquotient_le y hy π _ (isSmooth_prodIrr _ hd) (.of_surjective φ hφ)
  have hs : ∑ i, (dec (segLow Δ a h0) i).1 = u.1 := by rw [sum_dec_fst, hu1]
  have ht : ∑ i, (dec (segHigh Δ a h1) i).1 = v.1 := by rw [sum_dec_fst, hv1]
  exact GlobalTheory.TL.derivative_cuspidal_pair_length hA u v _ _ hs ht Δ.d (fun _ => rfl) (fun _ => rfl) (isCusp_dec _) (isCusp_dec _)
    (fine_tensor hA _ hlow u hu hs) (fine_tensor hA _ hhigh v hv ht) hd y hy hyc (h.trans hle)

theorem fineJac_step (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (h3 : 3 ≤ Δ.len)
    (ih : ∀ Δ' : Segment k, Δ'.len < Δ.len → FineJac Δ') : FineJac Δ := by
  intro N V _ _ π hπ
  obtain ⟨hd0, hc⟩ := id hπ
  have hsub := hc.isSubquotient
  have hsm : IsSmooth π := hsub.isSmooth (isSmooth_prodIrr _ _)
  have hN : N = Δ.len * Δ.d := by
    rw [← hd0, Segment.sum_term_fst]
    rfl
  have shape : ∀ (c : ℕ) (y : Fin c → IrrGL k) (hy : ∑ a, (y a).1 = N), (∀ a, (y a).IsCusp) → 1 ≤ jm y hy π →
      ∃ h : c = Δ.len, ∀ a, y a = dec Δ (Fin.cast h a) := by
    intro c y hy hyc h
    have hl1 : 1 < Δ.len := by omega
    have hl2 : Δ.len - 1 < Δ.len := by omega
    have hl0 : 0 < Δ.len - 1 := by omega
    obtain ⟨f₁, g₁, dis₁, hf₁, hg₁⟩ := shuffle_step hA Δ π hπ 1 one_pos hl1
      (ih _ (show 1 < Δ.len from hl1)) (ih _ (show Δ.len - 1 < Δ.len from hl2)) y hy hyc h
    obtain ⟨f₂, g₂, dis₂, hf₂, hg₂⟩ := shuffle_step hA Δ π hπ (Δ.len - 1) hl0 hl2
      (ih _ (show Δ.len - 1 < Δ.len from hl2)) (ih _ (show Δ.len - (Δ.len - 1) < Δ.len by omega)) y hy hyc h
    have hpos : ∀ a, 0 < (y a).1 := fun a => (hyc a).1
    obtain ⟨cov₁, hc₁⟩ := cover (p := 1) (q := Δ.len - 1) (d := Δ.d) (fun a => (y a).1) hpos
      (by rw [hy, hN, Nat.add_sub_cancel' hl1.le]) f₁ g₁ f₁.injective g₁.injective dis₁
      (fun i => congrArg Sigma.fst (hf₁ i)) (fun i => congrArg Sigma.fst (hg₁ i))
    obtain ⟨cov₂, -⟩ := cover (p := Δ.len - 1) (q := Δ.len - (Δ.len - 1)) (d := Δ.d) (fun a => (y a).1) hpos
      (by rw [hy, hN, Nat.add_sub_cancel' hl2.le]) f₂ g₂ f₂.injective g₂.injective dis₂
      (fun i => congrArg Sigma.fst (hf₂ i)) (fun i => congrArg Sigma.fst (hg₂ i))
    have hcl : c = Δ.len := by omega
    subst hcl
    have e : ∀ {m n : ℕ}, m = n → Δ.first.nu ((m : ℕ) : ℂ) = Δ.first.nu ((n : ℕ) : ℂ) := by
      rintro m _ rfl
      rfl
    have hinj : ∀ a b, a < Δ.len → b < Δ.len →
        Δ.first.nu ((a : ℕ) : ℂ) = Δ.first.nu ((b : ℕ) : ℂ) → a = b := fun a b ha hb hab =>
      congrArg Fin.val (GlobalTheory.T.segment_term_injective hA Δ (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab)
    have z₁ : 0 < (segLow Δ 1 one_pos).len := one_pos
    have z₂ : 0 < (segHigh Δ (Δ.len - 1) hl2).len := by
      show 0 < Δ.len - (Δ.len - 1)
      omega
    refine ⟨rfl, fun a => ?_⟩
    refine (word_eq_decreasing Δ.len h3 (fun n => Δ.first.nu ((n : ℕ) : ℂ)) hinj y
      (f₁ ⟨0, z₁⟩) g₁ (fun a => ?_) ?_ (fun j => ?_) (g₂ ⟨0, z₂⟩) f₂ (fun a => ?_) ?_ (fun j => ?_) a).trans ?_
    · rcases cov₁ a with ⟨x, rfl⟩ | h
      · have hx : (x : ℕ) < 1 := x.2
        exact Or.inl (congrArg f₁ (Fin.ext (by show (x : ℕ) = 0; omega)))
      · exact Or.inr h
    · exact (hf₁ _).trans ((dec_segLow _ _ _ _).trans (e (by simp)))
    · have hj := j.2
      exact (hg₁ j).trans ((dec_segHigh _ _ _ _).trans (e (by
        have : ((j : Fin (segHigh Δ 1 hl1).len) : ℕ) = j := rfl
        omega)))
    · rcases cov₂ a with h | ⟨x, rfl⟩
      · exact Or.inr h
      · have hx : (x : ℕ) < Δ.len - (Δ.len - 1) := x.2
        exact Or.inl (congrArg g₂ (Fin.ext (by show (x : ℕ) = 0; omega)))
    · exact (hg₂ _).trans ((dec_segHigh _ _ _ _).trans (e (by simp; omega)))
    · have hj := j.2
      exact (hf₂ j).trans ((dec_segLow _ _ _ _).trans (e (by
        have : ((j : Fin (segLow Δ (Δ.len - 1) hl0).len) : ℕ) = j := rfl
        omega)))
    · have ha := a.2
      have e₂ : ((Fin.rev (Fin.cast rfl a) : Fin Δ.len) : ℕ) = Δ.len - 1 - a := by
        rw [Fin.val_rev]
        simp only [Fin.val_cast]
        omega
      show _ = Δ.first.nu (((Fin.rev (Fin.cast rfl a) : Fin Δ.len) : ℕ) : ℂ)
      rw [e₂]
  refine ⟨fun hd => ?_, shape⟩
  have hinj := GlobalTheory.T.segment_term_injective hA Δ
  have hset : {e : Fin Δ.len ≃ Fin Δ.len | ∀ a, dec Δ a = Δ.term (e a)} = {Fin.revPerm} := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      exact Equiv.ext fun a => (hinj (h a)).symm
    · rintro rfl a
      rfl
  have hup : jm (dec Δ) hd π ≤ 1 := by
    refine (GlobalTheory.T.jacquet_multiplicity_subquotient_le (dec Δ) hd π _ (isSmooth_prodIrr _ hd0) hsub).trans ?_
    rw [GlobalTheory.T.jacquet_multiplicity_cuspidal_product hA Δ.term (dec Δ) hd0 hd Δ.isCusp_term (isCusp_dec Δ), hset, Set.ncard_singleton]
    simp
  obtain ⟨e, he, h1⟩ := GlobalTheory.T.irreducible_subquotient_cuspidal_permutation hA Δ.term hd0 Δ.isCusp_term π hsm hc.1 hsub
  obtain ⟨h, hh⟩ := shape Δ.len _ he (fun a => Δ.isCusp_term _) h1
  have hfun : (fun a => Δ.term (e a)) = dec Δ := funext fun a => hh a
  rw [jm_congr hfun he hd] at h1
  exact le_antisymm hup h1

end GlobalTheory.CompanionTheory.LkSegFine

end
end

section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
theorem _root_.GlobalTheory.TL.fine_jacquet_segment_induction : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (h3 : 3 ≤ Δ.len) (ih : ∀ Δ' : Segment k, Δ'.len < Δ.len → FineJac Δ'), FineJac Δ := by
  first | exact @GlobalTheory.CompanionTheory.LkSegFine.fineJac_step | exact GlobalTheory.CompanionTheory.LkSegFine.fineJac_step
end
