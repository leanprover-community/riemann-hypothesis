import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.CasselmanSuffTemp
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TCells
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TScalarFull
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TSchur
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInSupportOfMultiProd
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TUnitcent

section
open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

theorem UpperTheory.Lit.Cas.scalarProd :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h : ℕ) (y : Fin h → IrrGL k) (x : IrrGL k) (hc : ∑ i, (y i).1 = x.1) (t : kˣ) (c : Fin h → ℂ), (∀ i, ScalarBy (y i) t (c i)) → jhMult x.rep (prodIrr y hc) ≠ 0 → ScalarBy x t (∏ i, c i) := by
  intro k _ _ _ _ h y x hc t c hy hm w
  exact GlobalTheory.SmGL.Model.scalar_of_isSubquotient (jhMult_ne_zero_iff.1 hm)
    (UpperTheory.Lit.Cas.scalarFull k h x.1 y hc t c hy) w
end

section
open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

namespace UpperTheory.Lit.Cas.TSplit

private theorem subQuot_apply_of_smul {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (S T : Subrepresentation ρ) {g : G} {c : ℂ}
    (h : ∀ v, ρ g v = c • v) (y : S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) :
    subQuot S T g y = c • y := by
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hs : S.toRepresentation g s = c • s := Subtype.ext (h s)
  show Submodule.Quotient.mk (S.toRepresentation g s) = _
  rw [hs, Submodule.Quotient.mk_smul]

private theorem exists_step_of_jhMult_ne_zero {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V}
    (h : jhMult σ ρ ≠ 0) :
    ∃ S T : Subrepresentation ρ, Nonempty ((subQuot S T).Equiv σ) := by
  by_contra hne
  apply h
  unfold jhMult
  refine nonpos_iff_eq_zero.mp (iSup_le fun r => iSup_le fun hr => ?_)
  obtain ⟨S, T, -, -, hST⟩ := hr
  cases r with
  | zero => simp
  | succ n => exact (hne ⟨S 0, T 0, hST 0⟩).elim

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem leviEmb_scalar {s N : ℕ} (d : Fin s → ℕ) (hd : ∑ a, d a = N) (t : kˣ) :
    leviEmb k (stdBlocks d hd) (fun a => Matrix.GeneralLinearGroup.scalar (Fin (d a)) t) =
      Matrix.GeneralLinearGroup.scalar (Fin N) t := by
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks d hd).surjective j
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  · rw [leviEmb_apply_ne _ _ _ hab]
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
    exact fun h => absurd h hab

private theorem nabs_det_scalar (n : ℕ) (t : kˣ) :
    nabs k (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin n) t)) =
      nabs k t ^ n := by
  have : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin n) t) = t ^ n := by
    ext; simp [Matrix.GeneralLinearGroup.scalar]
  rw [this]
  simp [nabs]

private theorem deltaHalf_scalar (d : Fin 2 → ℕ) (t : kˣ) :
    deltaHalf k (fun a => Fin (d a))
      (fun a => Matrix.GeneralLinearGroup.scalar (Fin (d a)) t) = 1 := by
  ext
  rw [val_deltaHalf]
  have hm : modulus k (fun a => Fin (d a))
      (fun a => Matrix.GeneralLinearGroup.scalar (Fin (d a)) t) = 1 := by
    simp only [modulus, Fin.prod_univ_two, nabs_det_scalar, modExp]
    simp only [Finset.sum_filter, Fin.sum_univ_two]
    simp
    have hp : nabs k t ≠ 0 := ne_of_gt (nabs_pos' k t)
    have he : (nabs k t ^ d 1) ^ d 0 = nabs k t ^ (((d 0 : ℕ) : ℤ) * ((d 1 : ℕ) : ℤ)) := by
      rw [mul_comm, zpow_mul, zpow_natCast, zpow_natCast]
    have he' : (nabs k t ^ d 0) ^ d 1 = nabs k t ^ (((d 0 : ℕ) : ℤ) * ((d 1 : ℕ) : ℤ)) := by
      rw [zpow_mul, zpow_natCast, zpow_natCast]
    rw [he, he']
    exact mul_inv_cancel₀ (zpow_ne_zero _ hp)
  rw [hm]
  simp

private theorem piTensor_apply_of_smul {h : ℕ} (x : Fin h → IrrGL k) (g : ∀ a, GL (Fin (x a).1) k)
    (c : Fin h → ℂ) (hc : ∀ a v, (x a).rep (g a) v = c a • v)
    (w : PiTensorProduct ℂ (fun a => (x a).2.rep.V)) :
    piTensor (fun a => (x a).rep) g w = (∏ a, c a) • w := by
  induction w using PiTensorProduct.induction_on with
  | add y z hy hz => rw [map_add, hy, hz, smul_add]
  | smul_tprod r y =>
    rw [map_smul, piTensor_tprod, smul_comm]
    congr 1
    simp only [hc]
    exact MultilinearMap.map_smul_univ _ _ _

private theorem smul_eq_of_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [Nontrivial W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (E : ρ.Equiv σ) {g : G} {c c' : ℂ} (hρ : ∀ v, ρ g v = c • v) (hσ : ∀ w, σ g w = c' • w) :
    c' = c := by
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  have key : E.toLinearEquiv (ρ g (E.toLinearEquiv.symm w)) =
      σ g (E.toLinearEquiv (E.toLinearEquiv.symm w)) :=
    Representation.IntertwiningMap.isIntertwining ρ σ E.toIntertwiningMap g _
  simp only [hρ, hσ, map_smul, LinearEquiv.apply_symm_apply] at key
  have h0 : (c' - c) • w = 0 := by rw [sub_smul, key, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right hw)

end UpperTheory.Lit.Cas.TSplit

open UpperTheory.Lit.Cas.TSplit in
theorem UpperTheory.Lit.Cas.split :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (x : Fin 2 → IrrGL k) (hd : ∑ a, (x a).1 = N), jm x hd π ≠ 0 → ∀ (t : kˣ) (c c0 c1 : ℂ), (∀ v, π (Matrix.GeneralLinearGroup.scalar (Fin N) t) v = c • v) → ScalarBy (x 0) t c0 → ScalarBy (x 1) t c1 → c0 * c1 = c := by
  intro k _ _ _ _ N V _ _ π x hd hj t c c0 c1 hπ h0 h1
  obtain ⟨S, T, ⟨E⟩⟩ := exists_step_of_jhMult_ne_zero hj
  set g : Levi k (fun a => Fin (x a).1) := fun a => Matrix.GeneralLinearGroup.scalar (Fin (x a).1) t
  have hjac : ∀ v, jac (stdBlocks (fun a => (x a).1) hd) π g v = c • v := by
    intro v
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    rw [jac_mk, leviEmb_scalar, deltaHalf_scalar, hπ, inv_one, Units.val_one, one_smul,
      Submodule.Quotient.mk_smul]
  have hsub := subQuot_apply_of_smul S T hjac
  have hpi := piTensor_apply_of_smul x g ![c0, c1] (by
    intro a v
    fin_cases a
    · exact h0 v
    · exact h1 v)
  haveI : Nontrivial (PiTensorProduct ℂ (fun a => (x a).2.rep.V)) :=
    GlobalTheory.ProdSupport.nontrivial_piTensor _ (fun a => Model.nontrivial_of_isIrreducible (x a).2.rep.irr)
  have := smul_eq_of_equiv E hsub hpi
  simpa [Fin.prod_univ_two] using this
end

section
open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

private theorem jac_equiv_of_equiv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL n k) V} {τ : Representation ℂ (GL n k) W} (φ : π.Equiv τ) :
    Nonempty ((jac e π).Equiv (jac e τ)) := by
  refine ⟨Representation.Equiv.mk' (jacMap e φ.toIntertwiningMap)
    (jacMap e φ.symm.toIntertwiningMap) ?_ ?_⟩
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H v =>
      change Submodule.Quotient.mk (φ.symm (φ v)) = Submodule.Quotient.mk v
      simp
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H v =>
      change Submodule.Quotient.mk (φ (φ.symm v)) = Submodule.Quotient.mk v
      simp

private theorem cell_exp (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hC : CasselmanNecSq k) (δ : IrrGL k)
    (h1 : 1 ≤ δ.1) (h2 : IsSqIntCoeff δ.rep) (y : Fin 2 → IrrGL k) (hr : ∑ j, (y j).1 = δ.1)
    (hj : jm y hr δ.rep ≠ 0) (t : kˣ) (ht : Tendsto (fun n : ℕ => (t : k) ^ n) atTop (𝓝 0))
    (a : Fin 2 → ℂ) (ha : ∀ j, ScalarBy (y j) t (a j)) : ‖a 0‖ ≤ 1 ∧ ‖a 0‖ * ‖a 1‖ = 1 := by
  obtain ⟨⟨c, hc⟩, -, -⟩ := schur hA k δ t
  have hu : ‖c‖ = 1 := unitcent k δ.1 _ δ.rep 2 δ.snd.rep.smooth δ.snd.rep.irr h2 t c hc
  have hprod : a 0 * a 1 = c := split k δ.1 _ δ.rep y hr hj t c (a 0) (a 1) hc (ha 0) (ha 1)
  have hnorm : ‖a 0‖ * ‖a 1‖ = 1 := by rw [← norm_mul, hprod, hu]
  refine ⟨?_, hnorm⟩
  by_cases h0 : (y 0).1 = 0
  · rw [(schur hA k (y 0) t).2.2 (a 0) h0 (ha 0), norm_one]
  by_cases h1' : (y 1).1 = 0
  · rw [(schur hA k (y 1) t).2.2 (a 1) h1' (ha 1), norm_one, mul_one] at hnorm
    exact hnorm.le
  have hpos : ∀ j : Fin 2, 0 < (y j).1 :=
    Fin.forall_fin_two.2 ⟨Nat.pos_of_ne_zero h0, Nat.pos_of_ne_zero h1'⟩
  have hE := hC δ.1 δ.rep h1 δ.snd.rep.smooth δ.snd.rep.irr h2 2 y hr hpos hj
  have hlt := (hE t ht a ha).1 0 (by norm_num)
  have hf : (Finset.univ.filter fun i : Fin 2 => i ≤ 0) = {0} := by decide
  rw [hf, Finset.prod_singleton] at hlt
  exact hlt.le

theorem UpperTheory.Lit.Cas.prodExp :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], CasselmanNecSq k → ∀ (h N : ℕ) (δ : Fin h → IrrGL k) (hd : ∑ i, (δ i).1 = N), (∀ i, 1 ≤ (δ i).1 ∧ IsSqIntCoeff (δ i).rep) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), π.IsIrreducible → Nonempty (π.Equiv (prodIrr δ hd)) → UnitaryCentral π ∧ MaxExpWeak π := by
  intro hG hBZ hA k _ _ _ _ hC h N δ hd hδ V _ _ π hirr hφ
  obtain ⟨φ⟩ := hφ
  haveI := nontrivial_of_irreducible hirr
  constructor
  · intro t c hc
    choose b hb using fun i => (schur hA k (δ i) t).1
    have hbn : ∀ i, ‖b i‖ = 1 := fun i =>
      unitcent k (δ i).1 _ (δ i).rep 2 (δ i).snd.rep.smooth (δ i).snd.rep.irr (hδ i).2 t (b i) (hb i)
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hφv : φ.toLinearEquiv v ≠ 0 := by
      rwa [ne_eq, LinearEquiv.map_eq_zero_iff]
    have e1 : φ.toLinearEquiv (π (Matrix.GeneralLinearGroup.scalar (Fin N) t) v)
        = prodIrr δ hd (Matrix.GeneralLinearGroup.scalar (Fin N) t) (φ.toLinearEquiv v) :=
      LinearMap.congr_fun
        (φ.toIntertwiningMap.isIntertwining' (Matrix.GeneralLinearGroup.scalar (Fin N) t)) v
    have e2 : c • φ.toLinearEquiv v = (∏ i, b i) • φ.toLinearEquiv v :=
      calc c • φ.toLinearEquiv v = φ.toLinearEquiv (c • v) :=
            (LinearEquiv.map_smul φ.toLinearEquiv c v).symm
        _ = φ.toLinearEquiv (π (Matrix.GeneralLinearGroup.scalar (Fin N) t) v) :=
            congrArg _ (hc v).symm
        _ = prodIrr δ hd (Matrix.GeneralLinearGroup.scalar (Fin N) t) (φ.toLinearEquiv v) := e1
        _ = (∏ i, b i) • φ.toLinearEquiv v := scalarFull k h N δ hd t b hb _
    have hcb : c = ∏ i, b i := smul_left_injective ℂ hφv e2
    rw [hcb, norm_prod]
    exact Finset.prod_eq_one (fun i _ => hbn i)
  · intro x hx hpos hj
    have hjm : jm x hx (prodIrr δ hd) ≠ 0 := by
      obtain ⟨ψ⟩ := jac_equiv_of_equiv (stdBlocks (fun a => (x a).1) hx) φ
      unfold jm at hj ⊢
      rwa [← jhMult_congr_right _ ψ]
    obtain ⟨y, hr, hcc, hyj, hxj⟩ := cells hG hBZ k h N δ hd x hx hjm
    intro t ht c hcx
    choose a ha using fun i j => (schur hA k (y i j) t).1
    have hcj : ∀ j, c j = ∏ i, a i j := fun j =>
      (schur hA k (x j) t).2.1 _ _ (hcx j)
        (scalarProd k h (fun i => y i j) (x j) (hcc j) t (fun i => a i j) (fun i => ha i j) (hxj j))
    have hcell : ∀ i, ‖a i 0‖ ≤ 1 ∧ ‖a i 0‖ * ‖a i 1‖ = 1 := fun i =>
      cell_exp hA hC (δ i) (hδ i).1 (hδ i).2 (y i) (hr i) (hyj i) t ht (a i) (ha i)
    have n0 : ‖c 0‖ ≤ 1 := by
      rw [hcj 0, norm_prod]
      exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => (hcell i).1)
    have n01 : ‖c 0‖ * ‖c 1‖ = 1 := by
      rw [hcj 0, hcj 1, norm_prod, norm_prod, ← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one (fun i _ => (hcell i).2)
    refine ⟨fun j hj' => ?_, by rw [Fin.prod_univ_two]; exact n01⟩
    have hj0 : j = 0 := Fin.ext (by omega)
    subst hj0
    have hf : (Finset.univ.filter fun i : Fin 2 => i ≤ 0) = {0} := by decide
    rw [hf, Finset.prod_singleton]
    exact n0
end
