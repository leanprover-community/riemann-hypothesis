import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulVec
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteSupport
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalIsGeneric
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerCharEqOneOfMemUnipRad
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairIterPhiMir
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativePreservesSubquotient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EquivariantFunctionalsEqDualAnnihilator
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedEqFixedVectors
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipBEqUnipotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalInvTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspProdCharTransport
import GroundTheory.AutomorphicForms.ContragredientTranspose
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumFilterSuperdiag

section
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir ValuativeRel
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.DerExhaust

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem t2 : T2Space k := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  infer_instance

theorem isOpen_O : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer

theorem isCompact_O : IsCompact (𝒪[k] : Set k) := IsNonarchimedeanLocalField.isCompact_closedBall k 1

theorem exists_ne_zero_mem {U : Set k} (hU : U ∈ 𝓝 (0 : k)) : ∃ z : k, z ≠ 0 ∧ z ∈ U := by
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff U).mp hU
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero k)
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact γ.ne_zero (by simpa using hy.symm)
  obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have hr0 : r ≠ 0 := by simpa using hr
  refine ⟨r * y, mul_ne_zero hr0 hy0, hγ ?_⟩
  show valuation k (r * y) < γ
  rw [map_mul, hy]
  exact mul_lt_of_lt_one_left (by simp [zero_lt_iff]) hr1

variable (k) in

def intGL (N : ℕ) : Subgroup (GL (Fin N) k) where
  carrier := {g | ∀ i j, (g : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k] ∧
    ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k]}
  mul_mem' {a b} ha hb := by
    intro i j
    simp only [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_apply]
    exact ⟨Subring.sum_mem _ fun l _ => Subring.mul_mem _ (ha i l).1 (hb l j).1,
      Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hb i l).2 (ha l j).2⟩
  one_mem' := by
    intro i j
    simp only [inv_one, Units.val_one, Matrix.one_apply, and_self]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  inv_mem' {a} ha := by
    intro i j
    simpa [and_comm] using ha i j

theorem isCompact_intGL (N : ℕ) : IsCompact (intGL k N : Set (GL (Fin N) k)) := by
  haveI := t2 (k := k)
  let S : Set (Matrix (Fin N) (Fin N) k) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => (𝒪[k] : Set k)
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_O
  have hS' : IsCompact (S ×ˢ (MulOpposite.op '' S)) :=
    hS.prod (hS.image MulOpposite.continuous_op)
  convert Units.isClosedEmbedding_embedProduct.isCompact_preimage hS' using 1
  ext g
  constructor
  · intro h
    refine ⟨fun i _ j _ => (h i j).1, ⟨_, fun i _ j _ => (h i j).2, rfl⟩⟩
  · rintro ⟨h1, ⟨x, hx, hxe⟩⟩ i j
    have hx' : x = ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) := MulOpposite.op_injective hxe
    subst hx'
    exact ⟨h1 i (Set.mem_univ _) j (Set.mem_univ _), hx i (Set.mem_univ _) j (Set.mem_univ _)⟩

theorem isClosed_derUnip (N n : ℕ) : IsClosed (derUnip k N n : Set (GL (Fin N) k)) := by
  haveI := t2 (k := k)
  have hv : Continuous fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) := Units.continuous_val
  have he : ∀ i j : Fin N, Continuous fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) i j :=
    fun i j => hv.matrix_elem i j
  have h1 : (unipB k (Fin N) : Set (GL (Fin N) k)) =
      (⋂ i, ⋂ j, ⋂ (_ : j < i), {g : GL (Fin N) k | (g : Matrix (Fin N) (Fin N) k) i j = 0}) ∩
        ⋂ i, {g : GL (Fin N) k | (g : Matrix (Fin N) (Fin N) k) i i = 1} := by
    ext g
    simp only [SetLike.mem_coe, mem_unipB, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  have h2 : (colFix k N n : Set (GL (Fin N) k)) =
      ⋂ i : Fin N, ⋂ (_ : (i : ℕ) < n),
        {g : GL (Fin N) k | (g : Matrix (Fin N) (Fin N) k).mulVec (Pi.single i 1) = Pi.single i 1} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  show IsClosed ((unipB k (Fin N) ⊓ colFix k N n : Subgroup _) : Set (GL (Fin N) k))
  rw [Subgroup.coe_inf, h1, h2]
  refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
  · exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq (he i j) continuous_const
  · exact isClosed_iInter fun i => isClosed_eq (he i i) continuous_const
  · exact isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_eq (hv.matrix_mulVec continuous_const) continuous_const

theorem conj_entry_mem {N : ℕ} (y : kˣ) (hy : (y : k) ∈ 𝒪[k]) {u : GL (Fin N) k}
    (hu : u ∈ unipB k (Fin N)) (hyu : ∀ i j, (y : k) * (u : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k])
    (i j : Fin N) :
    (((diagT k (Fin N) (fun l : Fin N => y ^ (l : ℕ)))⁻¹ * u *
      diagT k (Fin N) (fun l : Fin N => y ^ (l : ℕ)) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j
      ∈ 𝒪[k] := by
  obtain ⟨h0, h1⟩ := (mem_unipB k).1 hu
  rw [← map_inv, Units.val_mul, Units.val_mul, val_diagT, val_diagT, Matrix.mul_diagonal,
    Matrix.diagonal_mul]
  simp only [Pi.inv_apply, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
  have ha0 : (y : k) ≠ 0 := y.ne_zero
  rcases lt_trichotomy (i : ℕ) j with hij | hij | hij
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hij
    rw [hd]
    have e : ((y : k) ^ (i : ℕ))⁻¹ * (u : Matrix (Fin N) (Fin N) k) i j * (y : k) ^ ((i : ℕ) + d + 1) =
        ((y : k) * (u : Matrix (Fin N) (Fin N) k) i j) * (y : k) ^ d := by
      rw [pow_succ, pow_add]
      field_simp
    rw [e]
    exact Subring.mul_mem _ (hyu i j) (Subring.pow_mem _ hy d)
  · have : i = j := Fin.ext hij
    subst this
    rw [h1 i, mul_one, inv_mul_cancel₀ (pow_ne_zero _ ha0)]
    exact Subring.one_mem _
  · rw [h0 i j (Fin.lt_def.2 hij), mul_zero, zero_mul]
    exact Subring.zero_mem _

theorem exhaust : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N n : ℕ) (s : Finset (GL (Fin N) k)), (↑s : Set (GL (Fin N) k)) ⊆ derUnip k N n →
    ∃ L : Subgroup (GL (Fin N) k), L ≤ derUnip k N n ∧ (↑s : Set (GL (Fin N) k)) ⊆ L ∧
      IsCompact (L : Set (GL (Fin N) k)) := by
  intro k _ _ _ _ N n s hs
  have hmul : ∀ c : k, ∀ᶠ z in 𝓝 (0 : k), z * c ∈ 𝒪[k] := by
    intro c
    have h := (continuous_mul_right c).tendsto (0 : k)
    rw [zero_mul] at h
    exact h (isOpen_O.mem_nhds (Subring.zero_mem _))
  have hU : ∀ᶠ z in 𝓝 (0 : k), z ∈ 𝒪[k] ∧ ∀ g ∈ s, ∀ i j : Fin N,
      z * (g : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k] ∧
        z * ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k] :=
    (show ∀ᶠ z in 𝓝 (0 : k), z ∈ 𝒪[k] from isOpen_O.mem_nhds (Subring.zero_mem _)).and ((Filter.eventually_all_finset _).2 fun g _ =>
      Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (hmul _).and (hmul _))
  obtain ⟨y, hy0, hyO, hyS⟩ := exists_ne_zero_mem hU
  set t := diagT k (Fin N) (fun l : Fin N => (Units.mk0 y hy0) ^ (l : ℕ)) with ht
  refine ⟨(intGL k N).map (MulAut.conj t).toMonoidHom ⊓ derUnip k N n, inf_le_right, ?_, ?_⟩
  · intro g hg
    have hgu : g ∈ unipB k (Fin N) := (hs hg).1
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_map.2 ⟨t⁻¹ * g * t, ?_, ?_⟩, hs hg⟩
    · intro i j
      have hinv : (t⁻¹ * g * t)⁻¹ = t⁻¹ * g⁻¹ * t := by group
      rw [hinv]
      exact ⟨conj_entry_mem (Units.mk0 y hy0) hyO hgu (fun i j => (hyS g hg i j).1) i j,
        conj_entry_mem (Units.mk0 y hy0) hyO (inv_mem hgu) (fun i j => (hyS g hg i j).2) i j⟩
    · show t * (t⁻¹ * g * t) * t⁻¹ = g
      group
  · rw [Subgroup.coe_inf, Subgroup.coe_map]
    have hc : Continuous fun g : GL (Fin N) k => t * g * t⁻¹ := by fun_prop
    exact ((isCompact_intGL N).image hc).inter_right (isClosed_derUnip N n)

end GlobalTheory.CompanionTheory.DerExhaust
end
end

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_finite_set_compact_subgroup : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N n : ℕ) (s : Finset (GL (Fin N) k)), (↑s : Set (GL (Fin N) k)) ⊆ derUnip k N n → ∃ L : Subgroup (GL (Fin N) k), L ≤ derUnip k N n ∧ (↑s : Set (GL (Fin N) k)) ⊆ L ∧ IsCompact (L : Set (GL (Fin N) k)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.DerExhaust.exhaust
end

section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.PRep.DerExact

theorem isOpen_ker_derChar (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (hψ : Continuous ψ) (N n : ℕ) :
    IsOpen ((derChar k ψ N n).ker : Set (derUnip k N n)) := by
  classical
  obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_addChar_eq_one ψ hψ
  let F : derUnip k N n → k := fun u => ∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1 ∧ n ≤ (p.1 : ℕ),
    (u : GL (Fin N) k).val p.1 p.2
  have hF : Continuous F := by
    refine continuous_finsetSum _ fun p _ => ?_
    have h1 : Continuous fun u : derUnip k N n => ((u : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) :=
      Units.continuous_val.comp continuous_subtype_val
    exact (continuous_apply p.2).comp ((continuous_apply p.1).comp h1)
  have hsub : F ⁻¹' GlobalTheory.SplitWeil.cball s ⊆ ((derChar k ψ N n).ker : Set (derUnip k N n)) := by
    intro u hu
    simp only [SetLike.mem_coe, MonoidHom.mem_ker]
    show Circle.toUnits (ψ (F u)) = 1
    rw [hs _ hu, map_one]
  have h1 : F 1 = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    show ((1 : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) p.1 p.2 = 0
    rw [Units.val_one]
    exact Matrix.one_apply_ne fun e => by
      have := (Finset.mem_filter.1 hp).2.1; rw [e] at this; omega
  have hmem : F ⁻¹' GlobalTheory.SplitWeil.cball s ∈ nhds (1 : derUnip k N n) :=
    hF.continuousAt.preimage_mem_nhds (by rw [h1]; exact GlobalTheory.SplitWeil.cball_mem_nhds s)
  exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset hmem hsub)

end GlobalTheory.CompanionTheory.PRep.DerExact
end

section
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair

noncomputable section
namespace GlobalTheory.CompanionTheory.StabForm

section General
variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def subRep (ρ : Representation ℂ G V) (S : Submodule ℂ V) (h : ∀ g, ∀ v ∈ S, ρ g v ∈ S) : Representation ℂ G S where
  toFun g := (ρ g).restrict (h g)
  map_one' := by ext v; simp
  map_mul' a b := by ext v; simp

def quotRep (ρ : Representation ℂ G V) (S : Submodule ℂ V) (h : ∀ g, ∀ v ∈ S, ρ g v ∈ S) : Representation ℂ G (V ⧸ S) where
  toFun g := S.mapQ S (ρ g) (h g)
  map_one' := by ext v; simp
  map_mul' a b := by ext v; simp

theorem isSmooth_subRep [TopologicalSpace G] (ρ : Representation ℂ G V) (S : Submodule ℂ V) (h : ∀ g, ∀ v ∈ S, ρ g v ∈ S)
    (hρ : IsSmooth ρ) : IsSmooth (subRep ρ S h) := fun v => by
  have : {g : G | subRep ρ S h g v = v} = {g : G | ρ g v.1 = v.1} := by
    ext g
    exact Subtype.ext_iff
  rw [this]
  exact hρ v.1

theorem isSmooth_quotRep [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation ℂ G V) (S : Submodule ℂ V) (h : ∀ g, ∀ v ∈ S, ρ g v ∈ S)
    (hρ : IsSmooth ρ) : IsSmooth (quotRep ρ S h) := fun x => by
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective S x
  rw [isOpen_iff_mem_nhds]
  intro g hg
  have hO : IsOpen ((fun y => g⁻¹ * y) ⁻¹' {y : G | ρ y v = v}) :=
    (hρ v).preimage (continuous_const.mul continuous_id)
  refine Filter.mem_of_superset (hO.mem_nhds (by simp)) fun y hy => ?_
  have hy' : ρ (g⁻¹ * y) v = v := hy
  have e : ρ y v = ρ g (ρ (g⁻¹ * y) v) := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  have hg' : S.mkQ (ρ g v) = S.mkQ v := hg
  show S.mkQ (ρ y v) = S.mkQ v
  rw [e, hy', hg']

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem whitRankIrr : GlobalTheory.BZSeg.WhitRankIrr k := by
  intro ψ hc h1 N V _ _ π hs hi
  have hadm : GroundTheory.Automorphic.IsAdmissible π :=
    (GlobalTheory.CompanionTheory.AdmDict.isAdmissible_iff π).1 (GlobalTheory.CompanionTheory.BZCuspPair.irrAdm k N V π hs hi)
  have hc0 : Continuous (Circle.coeHom.compAddChar ψ) := continuous_subtype_val.comp hc
  have h10 : Circle.coeHom.compAddChar ψ ≠ 1 := by
    intro h
    apply h1
    ext x
    have h2 : Circle.coeHom (ψ x) = 1 := by simpa using DFunLike.congr_fun h x
    have h3 : ((ψ x : Circle) : ℂ) = 1 := h2
    simpa using h3
  haveI := hi
  have hle := GroundTheory.Automorphic.ContragredientTranspose.rank_whittaker_le_one
    (Circle.coeHom.compAddChar ψ) hc0 h10 π hadm
  have cg : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ G V) {N N' : Subgroup G} (h : N = N') (χ : N → ℂ) (χ' : N' → ℂ)
      (hχ : ∀ u : N, χ u = χ' ⟨u, h ▸ u.2⟩),
      Module.rank ℂ (GroundTheory.Automorphic.Whittaker.equivariantFunctionals ρ χ) =
        Module.rank ℂ (GroundTheory.Automorphic.Whittaker.equivariantFunctionals ρ χ') := by
    intro G V _ _ _ ρ N N' h χ χ' hχ
    subst h
    have : χ = χ' := funext fun u => hχ u
    rw [this]
  rw [GlobalTheory.CompanionTheory.TwistedDual.rank_twJacquet_le_one_iff]
  rw [cg π (GlobalTheory.CompanionTheory.IwasawaDict.unipB_eq_unipotent k N) _
    (fun u => GroundTheory.Automorphic.Whittaker.psiN (Circle.coeHom.compAddChar ψ) (u : GL (Fin N) k))
    (fun u => GlobalTheory.CompanionTheory.WhitDict.whitChar_eq_psiN k ψ N u)]
  exact hle

theorem mir_reflect (ψ : AddChar k Circle) (hψ : Continuous ψ) (m n : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Mir k m) V) (σ : Representation ℂ (Mir k m) W)
    (hρ : IsSmooth ρ) (hσ : IsSmooth σ) (f : V →ₗ[ℂ] W) (hf : Function.Injective f)
    (hfi : ∀ g v, f (ρ g v) = σ g (f v)) (v : V)
    (hv : f v ∈ twKer σ (derUnipM k m n) (derCharM k ψ m n)) :
    v ∈ twKer ρ (derUnipM k m n) (derCharM k ψ m n) := by
  refine GlobalTheory.CompanionTheory.PRep.JacExact.twKer_reflect ρ σ hρ hσ _ _ ?_ ?_ f hf hfi v hv
  · have hc : Continuous (Subgroup.subgroupOfEquivOfLe (derUnip_le_Mir k m n)) :=
      Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
    exact (GlobalTheory.CompanionTheory.PRep.DerExact.isOpen_ker_derChar k ψ hψ (m + 1) n).preimage hc
  · intro s hs
    classical
    obtain ⟨L, hL, hsL, hLc⟩ := GlobalTheory.T.unipotent_finite_set_compact_subgroup k (m + 1) n (s.image Subtype.val) (by
      intro g hg
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hg
      obtain ⟨x, hx, rfl⟩ := hg
      exact hs hx)
    refine ⟨L.subgroupOf (Mir k m), fun x hx => hL (Subgroup.mem_subgroupOf.1 hx), ?_, ?_⟩
    · intro x hx
      exact Subgroup.mem_subgroupOf.2 (hsL (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_coe.1 hx))))
    · have hLM : L ≤ Mir k m := hL.trans (derUnip_le_Mir k m n)
      rw [Subtype.isCompact_iff]
      have : (Subtype.val '' ((L.subgroupOf (Mir k m) : Subgroup (Mir k m)) : Set (Mir k m))) = (L : Set (GL (Fin (m + 1)) k)) := by
        ext g
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact Subgroup.mem_subgroupOf.1 hx
        · intro hg
          exact ⟨⟨g, hLM hg⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩
      rw [this]
      exact hLc

abbrev mres {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (m + 1)) k) V) :
    Representation ℂ (Mir k m) V := (resM k π).ρ

theorem mres_twKer (ψ : AddChar k Circle) (m n : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (m + 1)) k) V) :
    twKer (mres π) (derUnipM k m n) (derCharM k ψ m n) = twKer π (derUnip k (m + 1) n) (derChar k ψ (m + 1) n) :=
  GlobalTheory.T.restriction_mirabolic_twisted_kernel k ψ m n V π

theorem twKer_ne_top_of_low (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (m : ℕ) {V : Type} [AddCommGroup V]
    [Module ℂ V] (τ : Representation ℂ (Mir k m) V) (hτ : IsSmooth τ) (hV : Nontrivial V)
    (h : ∀ n, 1 ≤ n → n ≤ m → twKer τ (derUnipM k m n) (derCharM k ψ m n) = ⊤) :
    twKer τ (derUnipM k m 0) (derCharM k ψ m 0) ≠ ⊤ := by
  obtain ⟨n, hn, ht⟩ := GlobalTheory.T.exists_nontrivial_derivative k ψ hc h1 m V τ hτ hV
  rcases Nat.eq_zero_or_pos n with rfl | hp
  · exact Submodule.Quotient.nontrivial_iff.1 ht
  · exact absurd (h n hp hn) (Submodule.Quotient.nontrivial_iff.1 ht)

theorem nontrivial_of_irr {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}
    (hi : π.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  obtain ⟨a, b, hab⟩ := hi.toNontrivial.exists_pair_ne
  apply hab
  ext x
  simp [Subsingleton.elim x 0]

theorem rank_top_le_one (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (m : ℕ) {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin (m + 1)) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible) :
    Module.rank ℂ (V ⧸ twKer (mres π) (derUnipM k m 0) (derCharM k ψ m 0)) ≤ 1 := by
  rw [mres_twKer ψ m 0 π, GlobalTheory.T.derivative_zero_whittaker_kernel k ψ (m + 1) V π]
  exact whitRankIrr ψ hc h1 (m + 1) V π hs hi

theorem whit_line (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (m : ℕ) {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin (m + 1)) k) V) (hcu : IsCuspidal π) (hi : π.IsIrreducible) :
    twKer (mres π) (derUnipM k m 0) (derCharM k ψ m 0) ≠ ⊤ ∧
    ∀ u w : V, u ∉ twKer (mres π) (derUnipM k m 0) (derCharM k ψ m 0) →
      ∃ c : ℂ, w - c • u ∈ twKer (mres π) (derUnipM k m 0) (derCharM k ψ m 0) := by
  have hg := GlobalTheory.CompanionTheory.BZDeriv.isGenericFor_of_isCuspidal k ψ hc h1 m V π hcu (nontrivial_of_irr hi)
  have hr := rank_top_le_one ψ hc h1 m π hcu.1 hi
  refine ⟨?_, fun u w hu => ?_⟩
  · rw [mres_twKer ψ m 0 π, GlobalTheory.T.derivative_zero_whittaker_kernel k ψ (m + 1) V π]
    exact Submodule.Quotient.nontrivial_iff.1 hg
  · set K := twKer (mres π) (derUnipM k m 0) (derCharM k ψ m 0)
    obtain ⟨v₀, hv₀⟩ := rank_le_one_iff.1 hr
    obtain ⟨r, hr⟩ := hv₀ (K.mkQ u)
    obtain ⟨s, hs⟩ := hv₀ (K.mkQ w)
    have hr0 : r ≠ 0 := by
      rintro rfl
      apply hu
      rw [zero_smul] at hr
      exact (Submodule.Quotient.mk_eq_zero K).1 hr.symm
    refine ⟨s / r, ?_⟩
    rw [← Submodule.Quotient.mk_eq_zero K]
    show K.mkQ (w - (s / r) • u) = 0
    rw [map_sub, map_smul, ← hr, ← hs, smul_smul, div_mul_cancel₀ _ hr0, sub_self]

theorem low_top (ψ : AddChar k Circle) (m : ℕ) {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin (m + 1)) k) V) (hcu : IsCuspidal π) (n : ℕ) (hn : 1 ≤ n) (hm : n ≤ m) :
    twKer (mres π) (derUnipM k m n) (derCharM k ψ m n) = ⊤ := by
  rw [mres_twKer ψ m n π]
  exact GlobalTheory.T.cuspidal_twisted_kernel_top k ψ (m + 1) n V π hcu hn (by omega)

theorem mir_irreducible (m : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (m + 1)) k) V)
    (hcu : IsCuspidal π) (hi : π.IsIrreducible) (S : Submodule ℂ V)
    (hS : ∀ (p : Mir k m), ∀ v ∈ S, (mres π) p v ∈ S) : S = ⊥ ∨ S = ⊤ := by
  obtain ⟨ψ, hc, h1⟩ := GlobalTheory.LocGL.exists_continuous_addChar_ne_one k
  by_contra hne
  push_neg at hne
  obtain ⟨hb, ht⟩ := hne
  have hT : IsSmooth (mres π) := GlobalTheory.CompanionTheory.BZCuspPair.isSmooth_resM hcu.1
  obtain ⟨-, hline⟩ := whit_line ψ hc h1 m π hcu hi
  have hlow := low_top ψ m π hcu
  have hSn : Nontrivial S := Submodule.nontrivial_iff_ne_bot.2 hb
  have hrefl : ∀ n, ∀ x : S, (x : V) ∈ twKer (mres π) (derUnipM k m n) (derCharM k ψ m n) →
      x ∈ twKer (subRep (mres π) S hS) (derUnipM k m n) (derCharM k ψ m n) := fun n x hx =>
    mir_reflect ψ hc m n _ (mres π) (isSmooth_subRep _ S hS hT) hT S.subtype Subtype.val_injective
      (fun g v => rfl) x hx
  have h₁ := twKer_ne_top_of_low ψ hc h1 m (subRep (mres π) S hS) (isSmooth_subRep _ S hS hT) hSn
    (fun n hn hnm => by
      rw [eq_top_iff]
      intro x _
      exact hrefl n x (by rw [hlow n hn hnm]; trivial))
  obtain ⟨s, hs⟩ := SetLike.exists_not_mem_of_ne_top _ h₁ rfl
  have hs' : (s : V) ∉ twKer (mres π) (derUnipM k m 0) (derCharM k ψ m 0) := fun h => hs (hrefl 0 s h)
  have hQn : Nontrivial (V ⧸ S) := Submodule.Quotient.nontrivial_iff.2 ht
  have hmap : ∀ n, ∀ x ∈ twKer (mres π) (derUnipM k m n) (derCharM k ψ m n),
      S.mkQ x ∈ twKer (quotRep (mres π) S hS) (derUnipM k m n) (derCharM k ψ m n) := fun n x hx =>
    twKer_le_comap_of (mres π) (quotRep (mres π) S hS) _ _ S.mkQ (fun g v => rfl) hx
  have h₂ := twKer_ne_top_of_low ψ hc h1 m (quotRep (mres π) S hS) (isSmooth_quotRep _ S hS hT) hQn
    (fun n hn hnm => by
      rw [eq_top_iff]
      rintro x -
      obtain ⟨w, rfl⟩ := S.mkQ_surjective x
      exact hmap n w (by rw [hlow n hn hnm]; trivial))
  apply h₂
  rw [eq_top_iff]
  rintro x -
  obtain ⟨w, rfl⟩ := S.mkQ_surjective x
  obtain ⟨c, hcw⟩ := hline s w hs'
  have e : S.mkQ w = S.mkQ (w - c • (s : V)) := by
    rw [map_sub, map_smul]
    have : S.mkQ (s : V) = 0 := (Submodule.Quotient.mk_eq_zero S).2 s.2
    rw [this, smul_zero, sub_zero]
  rw [e]
  exact hmap 0 _ hcw

theorem mir_scalar (m : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (m + 1)) k) V)
    (hcu : IsCuspidal π) (hi : π.IsIrreducible) (φ : V →ₗ[ℂ] V)
    (hφ : ∀ (p : Mir k m) v, φ ((mres π) p v) = (mres π) p (φ v)) : ∃ c : ℂ, φ = c • LinearMap.id := by
  obtain ⟨ψ, hc, h1⟩ := GlobalTheory.LocGL.exists_continuous_addChar_ne_one k
  obtain ⟨hK, hline⟩ := whit_line ψ hc h1 m π hcu hi
  set K := twKer (mres π) (derUnipM k m 0) (derCharM k ψ m 0) with hKdef
  obtain ⟨x₀, hx₀⟩ := SetLike.exists_not_mem_of_ne_top K hK rfl
  obtain ⟨c, hcx⟩ := hline x₀ (φ x₀) hx₀
  refine ⟨c, ?_⟩
  have hφK : ∀ x ∈ K, φ x ∈ K := fun x hx =>
    twKer_le_comap_of (mres π) (mres π) _ _ φ hφ hx
  let D : V →ₗ[ℂ] V := φ - c • LinearMap.id
  have hDK : ∀ w, D w ∈ K := by
    intro w
    obtain ⟨a, ha⟩ := hline x₀ w hx₀
    have e : D w = a • D x₀ + D (w - a • x₀) := by
      rw [← map_smul, ← map_add]
      congr 1
      abel
    rw [e]
    refine K.add_mem (K.smul_mem a hcx) ?_
    exact K.sub_mem (hφK _ ha) (K.smul_mem c ha)
  have hst : ∀ (p : Mir k m), ∀ v ∈ LinearMap.range D, (mres π) p v ∈ LinearMap.range D := by
    rintro p _ ⟨w, rfl⟩
    refine ⟨(mres π) p w, ?_⟩
    show φ _ - c • _ = (mres π) p (φ w - c • w)
    rw [hφ, map_sub, map_smul]
    rfl
  rcases mir_irreducible m π hcu hi _ hst with h | h
  · have : D = 0 := LinearMap.range_eq_bot.1 h
    exact sub_eq_zero.1 this
  · exfalso
    apply hK
    rw [eq_top_iff]
    rintro x -
    have : x ∈ LinearMap.range D := by rw [h]; trivial
    obtain ⟨w, rfl⟩ := this
    exact hDK w

theorem form_dichotomy {G X Y : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G X) (ρ' : Representation ℂ G Y) (β P : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (hβ : ∀ g a l, β (ρ g a) (ρ' g l) = β a l) (hP : ∀ g a l, P (ρ g a) (ρ' g l) = P a l)
    (hnd : ∀ x, x ≠ 0 → ∃ y, P x y ≠ 0)
    (hirr : ∀ S : Submodule ℂ X, (∀ g, ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤)
    (hend : ∀ φ : X →ₗ[ℂ] X, (∀ g v, φ (ρ g v) = ρ g (φ v)) → ∃ c : ℂ, φ = c • LinearMap.id) :
    (∃ c : ℂ, ∀ a l, β a l = c * P a l) ∨ ∀ x : X × X, x ≠ 0 → ∃ y, β x.1 y + P x.2 y ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hno, x, hx, hxy⟩ := hcon
  let R : Submodule ℂ (X × X) := LinearMap.ker (LinearMap.coprod β P)
  have memR : ∀ a b, (a, b) ∈ R ↔ ∀ y, β a y + P b y = 0 := by
    intro a b
    simp only [R, LinearMap.mem_ker, LinearMap.coprod_apply]
    exact LinearMap.ext_iff
  have hinv : ∀ g a b, (a, b) ∈ R → (ρ g a, ρ g b) ∈ R := by
    intro g a b h
    rw [memR] at h ⊢
    intro y
    have e : ρ' g (ρ' g⁻¹ y) = y := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [← e, hβ, hP]
    exact h _
  have hinj : ∀ b, (0, b) ∈ R → b = 0 := by
    intro b h
    by_contra hb
    obtain ⟨y, hy⟩ := hnd b hb
    have := (memR 0 b).1 h y
    simp at this
    exact hy this
  have hxR : (x.1, x.2) ∈ R := (memR _ _).2 hxy
  have hx1 : x.1 ≠ 0 := by
    intro h0
    apply hx
    have := hinj x.2 (h0 ▸ hxR)
    exact Prod.ext h0 this
  have hS : R.map (LinearMap.fst ℂ X X) = ⊤ := by
    rcases hirr (R.map (LinearMap.fst ℂ X X)) (by
      rintro g _ ⟨⟨a, b⟩, h, rfl⟩
      exact ⟨(ρ g a, ρ g b), hinv g a b h, rfl⟩) with h | h
    · exfalso
      apply hx1
      have : x.1 ∈ R.map (LinearMap.fst ℂ X X) := ⟨(x.1, x.2), hxR, rfl⟩
      rw [h] at this
      exact (Submodule.mem_bot ℂ).1 this
    · exact h
  let p : R →ₗ[ℂ] X := (LinearMap.fst ℂ X X).comp R.subtype
  have hpi : Function.Injective p := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨⟨a, b⟩, h⟩ h0
    have ha : a = 0 := h0
    subst ha
    have := hinj b h
    subst this
    rfl
  have hps : Function.Surjective p := by
    intro a
    have : a ∈ R.map (LinearMap.fst ℂ X X) := by rw [hS]; trivial
    obtain ⟨r, hr, rfl⟩ := this
    exact ⟨⟨r, hr⟩, rfl⟩
  let e := LinearEquiv.ofBijective p ⟨hpi, hps⟩
  let φ : X →ₗ[ℂ] X := (LinearMap.snd ℂ X X).comp (R.subtype.comp e.symm.toLinearMap)
  have hgraph : ∀ a, (a, φ a) ∈ R := by
    intro a
    have h1 : ((e.symm a : R) : X × X).1 = a := congrArg id (e.apply_symm_apply a)
    have h2 := (e.symm a).2
    have : ((e.symm a : R) : X × X) = (a, φ a) := Prod.ext h1 rfl
    rwa [this] at h2
  have huniq : ∀ a b b', (a, b) ∈ R → (a, b') ∈ R → b = b' := by
    intro a b b' h h'
    have := hinj (b - b') (by
      have h3 := R.sub_mem h h'
      simpa using h3)
    exact sub_eq_zero.1 this
  obtain ⟨c, hc⟩ := hend φ (fun g v => huniq _ _ _ (hgraph _) (hinv g v _ (hgraph v)))
  obtain ⟨a, l, hal⟩ := hno (-c)
  apply hal
  have h := (memR _ _).1 (hgraph a) l
  rw [hc] at h
  simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul, smul_eq_mul] at h
  linear_combination h

theorem pair_iter (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) :
    ∀ (j s : ℕ) (τ τ' : MRep k (0 + j)),
    IsSmooth τ.ρ → IsSmooth τ'.ρ → ∀ B : τ.V →ₗ[ℂ] τ'.V →ₗ[ℂ] ℂ,
    (∀ (p : Mir k (0 + j)) v v', B (τ.ρ p v) (τ'.ρ p v') =
      ((detChar (Fin (0 + j + 1)) (absPow k (s : ℂ)) (p : GL (Fin (0 + j + 1)) k) : ℂˣ) : ℂ) * B v v') →
    (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) →
    ∃ B' : (iterPhi k ψ j τ).V →ₗ[ℂ] (iterPhi k ψ⁻¹ j τ').V →ₗ[ℂ] ℂ, ∀ w, w ≠ 0 → ∃ w', B' w w' ≠ 0
  | 0, s, _, _, _, _, B, hB, hn => ⟨B, hn⟩
  | j + 1, s, τ, τ', hs, hs', B, hB, hn => by
    obtain ⟨B₁, hB₁, hn₁⟩ := GlobalTheory.CompanionTheory.MirPair.pairing_phi k ψ hc h1 (0 + j) s _ _ τ.ρ τ'.ρ hs hs' B hB hn
    exact pair_iter ψ hc h1 j (s + 1) (MRep.phiM k ψ τ) (MRep.phiM k ψ⁻¹ τ')
      (GlobalTheory.T.smooth_phi_minus k ψ _ _ _ hs) (GlobalTheory.T.smooth_phi_minus k ψ⁻¹ _ _ _ hs') B₁ hB₁ hn₁

theorem twKer_mir_zero {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k 0) V) :
    twKer τ (MirUin k 0) 1 = ⊥ := by
  refine Submodule.span_eq_bot.2 ?_
  rintro _ ⟨u, v, rfl⟩
  have hu : ((u : Mir k 0)) = 1 := GlobalTheory.CompanionTheory.BZMirDer.NonZero.mir_zero_eq_one _
  simp [hu]

theorem iterPhi_zero_equiv (ψ : AddChar k Circle) (j : ℕ) (τ : MRep k (0 + j)) :
    Nonempty ((τ.V ⧸ twKer τ.ρ (derUnipM k (0 + j) 0) (derCharM k ψ (0 + j) 0)) ≃ₗ[ℂ] (iterPhi k ψ j τ).V) := by
  obtain ⟨q, hs, hk, -⟩ := GlobalTheory.CompanionTheory.BZMirJac.iterPhi_quotient ψ 0 j τ
  refine ⟨(Submodule.quotEquivOfEq _ _ hk.symm).trans ((q.quotKerEquivOfSurjective hs).trans
    (Submodule.quotEquivOfEqBot _ (twKer_mir_zero _)))⟩

theorem rank_le_of_pairing (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (m : ℕ) (τ τ' : MRep k m)
    (hs : IsSmooth τ.ρ) (hs' : IsSmooth τ'.ρ) (B : τ.V →ₗ[ℂ] τ'.V →ₗ[ℂ] ℂ)
    (hB : ∀ (p : Mir k m) v v', B (τ.ρ p v) (τ'.ρ p v') = B v v')
    (hn : ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0)
    (hr : Module.rank ℂ (τ'.V ⧸ twKer τ'.ρ (derUnipM k m 0) (derCharM k ψ⁻¹ m 0)) ≤ 1) :
    Module.rank ℂ (τ.V ⧸ twKer τ.ρ (derUnipM k m 0) (derCharM k ψ m 0)) ≤ 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = 0 + j := ⟨m, (Nat.zero_add m).symm⟩
  obtain ⟨B', hB'⟩ := pair_iter ψ hc h1 j 0 τ τ' hs hs' B (fun p v v' => by
    rw [GlobalTheory.CompanionTheory.BZCuspPair.detChar_zero, one_mul]
    exact hB p v v') hn
  obtain ⟨e⟩ := iterPhi_zero_equiv ψ j τ
  obtain ⟨e'⟩ := iterPhi_zero_equiv ψ⁻¹ j τ'
  rw [e.rank_eq]
  rw [e'.rank_eq] at hr
  have hd := (GlobalTheory.CompanionTheory.TwistedDual.rank_le_one_iff_rank_dual_le_one _).1 hr
  refine le_trans (LinearMap.rank_le_of_injective B' ?_) hd
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  by_contra h0
  obtain ⟨w', h⟩ := hB' w h0
  exact h (by rw [hw]; rfl)

section Sum
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def sumRep (ρ : Representation ℂ G V) : Representation ℂ G (V × V) where
  toFun g := (ρ g).prodMap (ρ g)
  map_one' := by ext <;> simp
  map_mul' a b := by ext <;> simp

theorem isSmooth_sumRep [TopologicalSpace G] (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) : IsSmooth (sumRep ρ) := fun v => by
  have : {g : G | sumRep ρ g v = v} = {g : G | ρ g v.1 = v.1} ∩ {g : G | ρ g v.2 = v.2} := by
    ext g
    exact Prod.ext_iff
  rw [this]
  exact (hρ v.1).inter (hρ v.2)

theorem not_rank_sum_le_one (ρ : Representation ℂ G V) (N : Subgroup G) (θ : N →* ℂˣ) (h : twKer ρ N θ ≠ ⊤) :
    ¬ Module.rank ℂ ((V × V) ⧸ twKer (sumRep ρ) N θ) ≤ 1 := by
  intro hr
  set K := twKer ρ N θ
  have hle : twKer (sumRep ρ) N θ ≤ K.prod K := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨n, v, rfl⟩
    exact ⟨Submodule.subset_span ⟨n, v.1, rfl⟩, Submodule.subset_span ⟨n, v.2, rfl⟩⟩
  obtain ⟨x, hx⟩ := SetLike.exists_not_mem_of_ne_top K h rfl
  obtain ⟨v₀, hv₀⟩ := rank_le_one_iff.1 hr
  set L := twKer (sumRep ρ) N θ
  obtain ⟨a, ha⟩ := hv₀ (L.mkQ (x, 0))
  obtain ⟨b, hb⟩ := hv₀ (L.mkQ (0, x))
  have hmem : ((b • x, -(a • x)) : V × V) ∈ L := by
    rw [← Submodule.Quotient.mk_eq_zero L]
    show L.mkQ _ = 0
    have : ((b • x, -(a • x)) : V × V) = b • (x, 0) - a • (0, x) := by simp
    rw [this, map_sub, map_smul, map_smul, ← ha, ← hb, smul_smul, smul_smul, mul_comm, sub_self]
  have h1 := hle hmem
  have hb0 : b = 0 := by
    by_contra hne
    exact hx ((K.smul_mem_iff hne).1 h1.1)
  have ha0 : a = 0 := by
    by_contra hne
    exact hx ((K.smul_mem_iff hne).1 (K.neg_mem_iff.1 h1.2))
  subst ha0
  rw [zero_smul] at ha
  have := hle ((Submodule.Quotient.mk_eq_zero L).1 ha.symm)
  exact hx this.1

end Sum

theorem invTranspose_mulVec (m : ℕ) (p : Mir k m) :
    ((GlobalTheory.TypeTame.invTranspose (m + 1) (p : GL (Fin (m + 1)) k) : GL (Fin (m + 1)) k) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec (Pi.single (Fin.last m) 1) = Pi.single (Fin.last m) 1 := by
  rw [GlobalTheory.TypeTame.invTranspose_val, Matrix.mulVec_transpose]
  exact (p⁻¹).2

theorem form_unique {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : ℕ) (σ : IrrRep (GL (Fin (m + 1)) k)) (hc : IsCuspidal σ.ρ)
    (β : σ.V →ₗ[ℂ] smoothPart σ.ρ.dual →ₗ[ℂ] ℂ)
    (hβ : ∀ g : GL (Fin (m + 1)) k,
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec (Pi.single (Fin.last m) 1) = Pi.single (Fin.last m) 1 →
      ∀ a l, β (σ.ρ g a) (contra σ.ρ g l) = β a l) :
    ∃ c : ℂ, ∀ a l, β a l = c * (l : Module.Dual ℂ σ.V) a := by
  obtain ⟨ψ, hψ, h1⟩ := GlobalTheory.LocGL.exists_continuous_addChar_ne_one k
  have hψi : Continuous (⇑(ψ⁻¹ : AddChar k Circle)) := by
    have e : (⇑ψ⁻¹ : k → Circle) = fun x => ψ (-x) := funext fun x => AddChar.inv_apply ψ x
    rw [e]
    exact hψ.comp continuous_neg
  have hG := GlobalTheory.SqIntUnit.compactOpen_basis k (m + 1)
  have hsurj : Function.Surjective (GlobalTheory.TypeTame.invTranspose (R := k) (m + 1)) := fun g =>
    ⟨_, GlobalTheory.TypeTame.invTranspose_invTranspose (m + 1) g⟩
  have hcont := GlobalTheory.TypeTame.continuous_invTranspose (R := k) (m + 1)
  have hadm : IsAdmissible σ.ρ := GlobalTheory.CompanionTheory.BZCuspPair.irrAdm k (m + 1) _ σ.ρ σ.smooth σ.irr
  have hci : (contra σ.ρ).IsIrreducible := GlobalTheory.ContraRefl.contra_isIrreducible hG hadm σ.irr
  let A : Representation ℂ (GL (Fin (m + 1)) k) σ.V := σ.ρ.comp (GlobalTheory.TypeTame.invTranspose (m + 1))
  let Y : Representation ℂ (GL (Fin (m + 1)) k) (smoothPart σ.ρ.dual) := (contra σ.ρ).comp (GlobalTheory.TypeTame.invTranspose (m + 1))
  have hAc : IsCuspidal A := GlobalTheory.InvTransposeCusp.isCuspidal_comp_invTranspose k (m + 1) _ σ.ρ hc
  have hAi : A.IsIrreducible := GlobalTheory.FinGL.Transport.isIrreducible_comp σ.ρ _ hsurj σ.irr
  have hYi : Y.IsIrreducible := GlobalTheory.FinGL.Transport.isIrreducible_comp (contra σ.ρ) _ hsurj hci
  have hYs : IsSmooth Y := isSmooth_comp (isSmooth_contra σ.ρ) _ hcont
  let P : σ.V →ₗ[ℂ] smoothPart σ.ρ.dual →ₗ[ℂ] ℂ := (smoothPart σ.ρ.dual).subtype.flip
  have hPev : ∀ g a l, P (σ.ρ g a) (contra σ.ρ g l) = P a l := by
    intro g a l
    show (l : Module.Dual ℂ σ.V) (σ.ρ g⁻¹ (σ.ρ g a)) = (l : Module.Dual ℂ σ.V) a
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hnd : ∀ x, x ≠ 0 → ∃ y, P x y ≠ 0 := fun x hx => GlobalTheory.ContraRefl.exists_smooth_form_ne σ.smooth hG hx
  have hβ' : ∀ (p : Mir k m) a l, β (mres A p a) (mres Y p l) = β a l := fun p a l =>
    hβ _ (invTranspose_mulVec m p) a l
  have hP' : ∀ (p : Mir k m) a l, P (mres A p a) (mres Y p l) = P a l := fun p a l => hPev _ a l
  rcases form_dichotomy (mres A) (mres Y) β P hβ' hP' hnd (mir_irreducible m A hAc hAi)
    (fun φ hφ => mir_scalar m A hAc hAi φ hφ) with h | h
  · exact h
  · exfalso
    have hT := GlobalTheory.CompanionTheory.BZCuspPair.isSmooth_resM hAc.1
    have hY' := GlobalTheory.CompanionTheory.BZCuspPair.isSmooth_resM hYs
    have hr := rank_le_of_pairing ψ hψ h1 m ⟨σ.V × σ.V, sumRep (mres A)⟩ (resM k Y)
      (isSmooth_sumRep _ hT) hY' (LinearMap.coprod β P)
      (fun p v v' => by
        exact congrArg₂ (· + ·) (hβ' p v.1 v') (hP' p v.2 v'))
      (fun v hv => h v hv)
      (rank_top_le_one ψ⁻¹ hψi (inv_ne_one.2 h1) m Y hYs hYi)
    exact not_rank_sum_le_one (mres A) _ _ (whit_line ψ hψ h1 m A hAc hAi).1 hr

end GlobalTheory.CompanionTheory.StabForm
end
end

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_mirabolic_invariant_pairing_scalar : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : ℕ) (σ : IrrRep (GL (Fin (m + 1)) k)) (hc : IsCuspidal σ.ρ)
    (β : σ.V →ₗ[ℂ] smoothPart σ.ρ.dual →ₗ[ℂ] ℂ)
    (hβ : ∀ g : GL (Fin (m + 1)) k,
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec (Pi.single (Fin.last m) 1) = Pi.single (Fin.last m) 1 →
      ∀ a l, β (σ.ρ g a) (contra σ.ρ g l) = β a l),
    ∃ c : ℂ, ∀ a l, β a l = c * (l : Module.Dual ℂ σ.V) a := by
  atlas_forward_decl GlobalTheory.CompanionTheory.StabForm.form_unique
end
