import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartAct0
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TClParts
import Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.CharOfScalar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryPointProperties
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ExistsNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPsIrr

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Hi.OrdB
open GlobalTheory.PRep
section General
variable {G V : Type} [CommGroup G] [AddCommGroup V] [Module ℂ V]
private theorem pow_comm (ρ : Representation ℂ G V) (t g : G) (c : ℂ) (m : ℕ) (v : V) :
    ((ρ t - c • (1 : Module.End ℂ V)) ^ m) (ρ g v) = ρ g (((ρ t - c • (1 : Module.End ℂ V)) ^ m) v) := by
  have h : Commute (ρ t - c • (1 : Module.End ℂ V)) (ρ g) :=
    Commute.sub_left ((Commute.all t g).map ρ) ((Commute.one_left _).smul_left c)
  exact LinearMap.congr_fun (h.pow_left m).eq v
private theorem pow_mem (ρ : Representation ℂ G V) (N : Subrepresentation ρ) (t : G) (c : ℂ) (m : ℕ)
    (v : V) (hv : v ∈ N.toSubmodule) : ((ρ t - c • (1 : Module.End ℂ V)) ^ m) v ∈ N.toSubmodule := by
  induction m with
  | zero => simpa using hv
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, LinearMap.sub_apply]
    exact sub_mem (N.apply_mem_toSubmodule t ih) (N.toSubmodule.smul_mem c ih)
private theorem exists_nil {ρ : Representation ℂ G V} (hl : HasFiniteLength ρ) {x : V} (hx : x ≠ 0) :
    ∃ N : Subrepresentation ρ, N ≠ ⊤ ∧ ∀ (t : G) (c : ℂ), ρ t x = c • x →
      ∃ m : ℕ, ∀ v, ((ρ t - c • (1 : Module.End ℂ V)) ^ m) v ∈ N.toSubmodule := by
  haveI := ((hasFiniteLength_iff_wellFounded ρ).1 hl).1
  obtain ⟨N, hN, hmax⟩ := (wellFounded_gt (α := Subrepresentation ρ)).has_min {N | x ∉ N.toSubmodule}
    ⟨⊥, fun h => hx ((Submodule.mem_bot ℂ).1 h)⟩
  refine ⟨N, fun h => hN (by rw [h]; trivial), fun t c hc => ?_⟩
  set f := ρ t - c • (1 : Module.End ℂ V) with hf
  have hb : f x = 0 := by simp [hf, hc]
  let K : ℕ →o Subrepresentation ρ :=
    ⟨fun m => ⟨N.toSubmodule.comap (f ^ m), fun g v hv => by
        show (f ^ m) (ρ g v) ∈ N.toSubmodule
        rw [hf, pow_comm]
        exact N.apply_mem_toSubmodule g hv⟩,
      monotone_nat_of_le_succ fun m v hv => by
        show (f ^ (m + 1)) v ∈ N.toSubmodule
        rw [add_comm, pow_add, Module.End.mul_apply]
        exact pow_mem ρ N t _ 1 _ hv⟩
  obtain ⟨a, ha⟩ := WellFoundedGT.monotone_chain_condition K
  let R : Subrepresentation ρ := ⟨N.toSubmodule ⊔ LinearMap.range (f ^ a), fun g v hv => by
    obtain ⟨y, hy, _, ⟨z, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add]
    exact Submodule.add_mem_sup (N.apply_mem_toSubmodule g hy) ⟨ρ g z, by rw [hf, pow_comm]⟩⟩
  have hR : x ∉ R.toSubmodule := fun hv => by
    obtain ⟨y, hy, _, ⟨z, rfl⟩, h⟩ := Submodule.mem_sup.1 hv
    have h1 : z ∈ (K (1 + a)).toSubmodule := by
      show (f ^ (1 + a)) z ∈ N.toSubmodule
      rw [pow_add, Module.End.mul_apply, eq_sub_of_add_eq' h, map_sub, pow_one, hb, zero_sub, ← pow_one f]
      exact neg_mem (pow_mem ρ N t _ 1 _ hy)
    rw [← ha _ (by omega)] at h1
    exact hN (h ▸ add_mem hy h1)
  have hNR : N ≤ R := fun v hv => Submodule.mem_sup_left (S := N.toSubmodule) hv
  have hE : N = R := by
    by_contra hne
    exact hmax R hR (lt_of_le_of_ne hNR hne)
  refine ⟨a, fun v => ?_⟩
  rw [hE]
  exact Submodule.mem_sup_right ⟨v, rfl⟩
private theorem pow_eig {f : Module.End ℂ V} {v : V} {a : ℂ} (h : f v = a • v) (c : ℂ) (m : ℕ) :
    ((f - c • (1 : Module.End ℂ V)) ^ m) v = (a - c) ^ m • v := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, h, pow_succ, mul_smul, sub_smul]
    rfl
private theorem eq_of_gen {f : Module.End ℂ V} {v : V} {a c : ℂ} (h : f v = a • v) (h0 : v ≠ 0)
    (hv : v ∈ f.maxGenEigenspace c) : a = c := by
  obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hv
  rw [pow_eig h] at hm
  exact sub_eq_zero.1 (pow_eq_zero_iff'.1 ((smul_eq_zero.1 hm).resolve_right h0)).1
private theorem exists_eig [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (E : Submodule ℂ V) (hE0 : E ≠ ⊥)
    (hE : ∀ t, ∀ v ∈ E, ρ t v ∈ E) : ∃ χ : G →* ℂˣ, ∃ v ∈ E, v ≠ 0 ∧ ∀ t, ρ t v = (χ t : ℂ) • v := by
  obtain ⟨S, ⟨hS0, hSE, hS⟩, hmin⟩ := (wellFounded_lt (α := Submodule ℂ V)).has_min
    {S | S ≠ ⊥ ∧ S ≤ E ∧ ∀ t, ∀ v ∈ S, ρ t v ∈ S} ⟨E, hE0, le_rfl, hE⟩
  have : Nontrivial S := Submodule.nontrivial_iff_ne_bot.2 hS0
  have key : ∀ t, ∃ c : ℂ, ∀ v ∈ S, ρ t v = c • v := fun t => by
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((ρ t).restrict (hS t))
    obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
    have hw1 : ρ t w = c • (w : V) := congrArg Subtype.val hw.apply_eq_smul
    refine ⟨c, fun v hv => ?_⟩
    have h1 : S ⊓ Module.End.eigenspace (ρ t) c = S := by
      by_contra hne
      refine hmin _ ⟨?_, inf_le_left.trans hSE, ?_⟩ (lt_of_le_of_ne inf_le_left hne)
      · exact (Submodule.ne_bot_iff _).2 ⟨w, ⟨w.2, Module.End.mem_eigenspace_iff.2 hw1⟩,
          fun h => hw.2 (Subtype.ext h)⟩
      · rintro s x ⟨hx, hx'⟩
        refine ⟨hS s x hx, Module.End.mem_eigenspace_iff.2 ?_⟩
        rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul,
          Module.End.mul_apply, Module.End.mem_eigenspace_iff.1 hx', map_smul]
    rw [← h1] at hv
    exact Module.End.mem_eigenspace_iff.1 hv.2
  choose c hc using key
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hS0
  let c' : G →* ℂ :=
    { toFun := c
      map_one' := by
        have := hc 1 v hv
        rw [map_one, Module.End.one_apply] at this
        exact smul_left_injective ℂ hv0 (this.symm.trans (one_smul _ _).symm)
      map_mul' := fun s t => by
        have := hc (s * t) v hv
        rw [map_mul, Module.End.mul_apply, hc t v hv, map_smul, hc s v hv, smul_smul, mul_comm] at this
        exact smul_left_injective ℂ hv0 this.symm }
  exact ⟨c'.toHomUnits, v, hSE hv, hv0, fun t => hc t v hv⟩
private theorem le_gen [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (E : Submodule ℂ V)
    (hE : ∀ t, ∀ v ∈ E, ρ t v ∈ E) (μ : G →* ℂˣ)
    (h : ∀ χ : G →* ℂˣ, ∀ v ∈ E, v ≠ 0 → (∀ t, ρ t v = (χ t : ℂ) • v) → χ = μ) (t : G) :
    E ≤ Module.End.maxGenEigenspace (ρ t) (μ t : ℂ) := by
  rw [Submodule.eq_iSup_inf_genEigenspace (p := E) (f := ρ t) ⊤ (hE t)
    (Module.End.iSup_maxGenEigenspace_eq_top (ρ t))]
  refine iSup_le fun c => ?_
  by_cases h0 : E ⊓ Module.End.genEigenspace (ρ t) c ⊤ = ⊥
  · rw [h0]; exact bot_le
  obtain ⟨χ, v, hv, hv0, hχ⟩ := exists_eig ρ _ h0 fun s v hv => ⟨hE s v hv.1, by
    obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hv.2
    exact (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨m, by rw [pow_comm, hm, map_zero]⟩⟩
  rw [← h χ v hv.1 hv0 hχ, eq_of_gen (hχ t) hv0 hv.2]
  exact inf_le_right
variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace.SeparableSpace G]
private theorem exists_form {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (hl : HasFiniteLength ρ)
    {x : V} (hx : x ≠ 0) : ∃ μ : G →* ℂˣ, IsSmoothChar μ ∧ (∀ (t : G) (c : ℂ), ρ t x = c • x → (μ t : ℂ) = c) ∧
      ∃ l : V →ₗ[ℂ] ℂ, l ≠ 0 ∧ ∀ g v, l (ρ g v) = (μ g : ℂ) * l v := by
  obtain ⟨T, hT, hnil⟩ := exists_nil hl hx
  haveI := ((hasFiniteLength_iff_wellFounded ρ).1 hl).1
  obtain ⟨M, hM, hTM⟩ := (eq_top_or_exists_le_coatom T).resolve_left hT
  have hi := isIrreducible_subQuot hM.covBy_top
  let p : (⊤ : Subrepresentation ρ).toRepresentation.IntertwiningMap (subQuot ⊤ M) :=
    ⟨Submodule.mkQ _, fun _ => rfl⟩
  have hs : IsSmooth (subQuot ⊤ M) :=
    IsSubquotient.isSmooth ⟨⊤, p, Submodule.Quotient.mk_surjective _⟩ hρ
  obtain ⟨μ, hμ⟩ := GlobalTheory.TorusEigenform.exists_char_of_isIrreducible hs hi
  have hμM : ∀ g v, ρ g v - (μ g : ℂ) • v ∈ M.toSubmodule := fun g v => by
    have := hμ g (Submodule.Quotient.mk ⟨v, trivial⟩)
    exact (Submodule.Quotient.eq (M.toSubmodule.comap (⊤ : Subrepresentation ρ).toSubmodule.subtype)
      (x := ⟨ρ g v, trivial⟩) (y := ⟨(μ g : ℂ) • v, trivial⟩)).1 this
  have hM' : M.toSubmodule < ⊤ := lt_top_iff_ne_top.2 fun h =>
    hM.1 (Subrepresentation.toSubmodule_injective h)
  obtain ⟨l, hl0, hlM⟩ := Submodule.exists_le_ker_of_lt_top _ hM'
  have hle : ∀ g v, l (ρ g v) = (μ g : ℂ) * l v := fun g v => by
    have := hlM (hμM g v)
    rwa [LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at this
  obtain ⟨v, hv⟩ : ∃ v, l v ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hl0 (LinearMap.ext hn)
  refine ⟨μ, ?_, fun t c hc => ?_, l, hl0, hle⟩
  · refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset ((hρ v).mem_nhds (by simp)) ?_)
    intro g hg
    have hg' : ρ g v = v := hg
    have h := hle g v
    rw [hg'] at h
    exact Units.ext (mul_right_cancel₀ hv (h.symm.trans (one_mul _).symm))
  · obtain ⟨m, hm⟩ := hnil t c hc
    have h1 : ∀ m : ℕ, l (((ρ t - c • (1 : Module.End ℂ V)) ^ m) v) = ((μ t : ℂ) - c) ^ m * l v := fun m => by
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ', Module.End.mul_apply, LinearMap.sub_apply, map_sub, hle, LinearMap.smul_apply,
          Module.End.one_apply, map_smul, ih, smul_eq_mul]
        ring
    have h2 := hlM (hTM (hm v))
    rw [LinearMap.mem_ker, h1] at h2
    exact sub_eq_zero.1 (pow_eq_zero_iff'.1 ((mul_eq_zero.1 h2).resolve_right hv)).1
end General
section Abs
variable {G M : Type} [Group G] (I : Iwa G) [AddCommGroup M] [Module ℂ M] (π : Representation ℂ G M) (c : ℕ)
  (φ : I.T →* ℂˣ)
private theorem eig_le (hφ : ∀ t : I.T, (t : G) ∈ I.Tc c → φ t = 1) : I.eig π c φ ≤ fixd π (I.I1 c) := by
  intro v hv g hg
  obtain ⟨x, hx, t, ht, y, hy, rfl⟩ := (iwMem G I c g).2.1.1 hg
  have h := hv.2.2 ⟨t, I.Tc_le c ht⟩
  rw [hφ _ ht] at h
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hv.2.1 y hy, h]
  simpa using hv.1 x hx
private theorem inv_stab (hφ : ∀ t : I.T, (t : G) ∈ I.Tc c → φ t = 1) {a : G} (ha : a ∈ I.P) {v : M}
    (hv : v ∈ ⨅ j : ℕ, (I.eig π c φ).map (I.uOp π I.z ^ j)) :
    I.uOp π a v ∈ ⨅ j : ℕ, (I.eig π c φ).map (I.uOp π I.z ^ j) := by
  have st := ((uOpLevel G I ℂ M π c).2.2 φ hφ).1
  have key : ∀ (j : ℕ), ∀ w ∈ I.eig π c φ, I.uOp π a ((I.uOp π I.z ^ j) w) = (I.uOp π I.z ^ j) (I.uOp π a w) := by
    intro j
    induction j with
    | zero => intro w _; simp
    | succ j ih =>
      intro w hw
      rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih _ (st _ I.z_mem w hw),
        (uOpMul G I ℂ M π _ _ ha I.z_mem w hw.1).2.1, (uOpMul G I ℂ M π _ _ I.z_mem ha w hw.1).2.1,
        I.comm a (I.P_le a ha) I.z (I.P_le _ I.z_mem)]
  refine (Submodule.mem_iInf _).2 fun j => ?_
  obtain ⟨w, hw, rfl⟩ := (Submodule.mem_iInf _).1 hv j
  exact ⟨_, st a ha w hw, (key j w hw).symm⟩
private theorem inv_inj (hφ : ∀ t : I.T, (t : G) ∈ I.Tc c → φ t = 1) (hs : I.Smooth π)
    [FiniteDimensional ℂ (fixd π (I.I1 c))] {v : M}
    (hv : v ∈ ⨅ j : ℕ, (I.eig π c φ).map (I.uOp π I.z ^ j)) (h0 : v ∈ I.jacKer π) : v = 0 := by
  have st := ((uOpLevel G I ℂ M π c).2.2 φ hφ).1 _ I.z_mem
  haveI : FiniteDimensional ℂ (I.eig π c φ) := Submodule.finiteDimensional_of_le (eig_le I π c φ hφ)
  have hv0 : v ∈ I.eig π c φ := by simpa using (Submodule.mem_iInf _).1 hv 0
  let f : Module.End ℂ (I.eig π c φ) := (I.uOp π I.z).restrict st
  have hf : ∀ (j : ℕ) (x : I.eig π c φ), ((f ^ j) x : M) = (I.uOp π I.z ^ j) x := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih => intro x; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]; rfl
  obtain ⟨m, hm⟩ := (propCker G I ℂ M π hs v hv0.1).1 h0
  have h1 : (⟨v, hv0⟩ : I.eig π c φ) ∈ ⨆ j : ℕ, LinearMap.ker (f ^ j) :=
    Submodule.mem_iSup_of_mem m (Subtype.ext ((hf m _).trans hm))
  have h2 : (⟨v, hv0⟩ : I.eig π c φ) ∈ ⨅ j : ℕ, LinearMap.range (f ^ j) := by
    refine (Submodule.mem_iInf _).2 fun j => ?_
    obtain ⟨w, hw, e⟩ := (Submodule.mem_iInf _).1 hv j
    exact ⟨⟨w, hw⟩, Subtype.ext ((hf j _).trans e)⟩
  exact congrArg Subtype.val
    ((Submodule.disjoint_def.1 (LinearMap.isCompl_iSup_ker_pow_iInf_range_pow f).disjoint) _ h1 h2)
end Abs
section Num
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
private theorem tc_single (ψ : Fin n → kˣ →* ℂˣ) (i : Fin n) (x : kˣ) : torusChar ψ (Pi.mulSingle i x) = ψ i x := by
  rw [torusChar_apply, Finset.prod_eq_single i (fun j _ hj => by simp [Pi.mulSingle_eq_of_ne hj]) (by simp)]
  simp
private theorem num (ω : Fin n → kˣ →* ℂˣ) {j : ℕ} (hj : j ≤ n) :
    ((Nat.card 𝓀[k] ^ (j * (n - j)) : ℕ) : ℂ) *
      ((deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) fun i => unif k ^ (if (i : ℕ) < j then 1 else 0 : ℤ)) : ℂ) *
        (torusChar (fun i => ω i * absPow k (((n : ℂ) - 1) / 2))
          (fun i => unif k ^ (if (i : ℕ) < j then 1 else 0 : ℤ)) : ℂ)) = psEig ω j := by
  have hd : ∀ (t : Fin n → kˣ) i, Matrix.GeneralLinearGroup.det (leviTorus k (Fin n) t i) = t i := fun t =>
    congrFun ((leviTorus k (Fin n)).left_inv t)
  have hq : (Nat.card 𝓀[k] : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hn : ((nabs k (unif k) : ℝ) : ℂ) = (Nat.card 𝓀[k] : ℂ)⁻¹ := by
    rw [GlobalTheory.LGrp.nabs_eq_zpow, ord_eq_one GlAx.unif_spec]
    simp [resCard]
  have h1 : ∀ i : Fin n, ((absPow k ((modExp (fun _ : Fin n => Unit) i : ℂ) / 2)
        (unif k ^ (if (i : ℕ) < j then 1 else 0 : ℤ)) : ℂ) *
      ((ω i * absPow k (((n : ℂ) - 1) / 2)) (unif k ^ (if (i : ℕ) < j then 1 else 0 : ℤ)) : ℂ)) =
      (if (i : ℕ) < j then (ω i (unif k) : ℂ) * ((Nat.card 𝓀[k] : ℂ) ^ (i : ℕ))⁻¹ else 1) *
        (Nat.card 𝓀[k] : ℂ) ^ (if (i : ℕ) < j then -((n : ℤ) - 1 - 2 * (i : ℕ)) else 0) := by
    intro i
    split_ifs
    · rw [zpow_one, MonoidHom.mul_apply, Units.val_mul, mul_left_comm, ← Units.val_mul, ← MonoidHom.mul_apply,
        ← absPow_add, modExp_fin _ (fun _ => by simp), mul_assoc, val_absPow, hn,
        show ((((n : ℤ) - 1 - 2 * (i : ℕ) : ℤ) : ℂ) / 2 + ((n : ℂ) - 1) / 2) = (((n : ℤ) - 1 - (i : ℕ) : ℤ) : ℂ) by
          push_cast; ring, Complex.cpow_intCast, ← zpow_natCast, ← _root_.zpow_neg, ← zpow_add₀ hq, _root_.inv_zpow']
      congr 2
      ring
    · simp
  have hp : ∀ (s : Finset (Fin n)) (e : Fin n → ℤ),
      ∏ i ∈ s, (Nat.card 𝓀[k] : ℂ) ^ e i = (Nat.card 𝓀[k] : ℂ) ^ ∑ i ∈ s, e i := by
    intro s e
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ hq]
  have h2 : ∑ i : Fin n, (if (i : ℕ) < j then -((n : ℤ) - 1 - 2 * (i : ℕ)) else 0) = -((j * (n - j) : ℕ) : ℤ) := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < j then -((n : ℤ) - 1 - 2 * i) else 0), ← Finset.sum_filter,
      show (Finset.range n).filter (· < j) = Finset.range j by ext; simp; omega, Nat.cast_mul, Nat.cast_sub hj]
    clear h1
    generalize (n : ℤ) = N
    clear hj
    induction j with
    | zero => simp
    | succ j ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  rw [deltaHalf_apply, torusChar_apply, Units.coe_prod, Units.coe_prod, ← Finset.prod_mul_distrib]
  simp only [hd, h1]
  rw [Finset.prod_mul_distrib, hp, h2, psEig, Finset.prod_filter, Nat.cast_pow, _root_.zpow_neg, zpow_natCast]
  field_simp
end Num
end UpperTheory.V.Hi.OrdB
open GlobalTheory.PRep in
theorem UpperTheory.V.Hi.exists_principal_series_of_distinct_inv_ne_bot :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), GlobalTheory.PRep.IsSmooth π → π.IsIrreducible → ∀ (c : ℕ) (φ : (glIwa k n).T →* ℂˣ), (∀ i (y : Uo k), (y : kˣ) ∈ Uc k (c + 1) → φ (eT k n i y) = 1) → Distinct φ → invPart π c φ ≠ ⊥ → ∃ ω : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) ∧ IsInvOn φ ω ∧ Nonempty (π.Equiv (PS ω)) ∧ Module.finrank ℂ (invPart π c φ) = 1 ∧ ∀ v ∈ invPart π c φ, ∀ j ≤ n, (glIwa k n).uOp π (al k n j) v = psEig ω j • v := by
  intro H k _ _ _ _ n V _ _ π hπ hirr c φ hφ0 hD hne
  obtain ⟨hker, hsm, hI, -, -, -, -, hidx, -, hT⟩ := glBridge k n V π
  have hφ : ∀ t : (glIwa k n).T, (t : GL (Fin n) k) ∈ (glIwa k n).Tc c → φ t = 1 := fun t ht => by
    obtain ⟨y, hy, hy'⟩ := hT t
    have e : (t : GL (Fin n) k) ∈ φ.ker.map (glIwa k n).T.subtype := by
      rw [hy]
      refine list_prod_mem fun x hx => ?_
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      exact ⟨eT k n i (y i), hφ0 i _ (hy' c ht i), rfl⟩
    obtain ⟨s, hs, e⟩ := e
    exact (Subtype.ext e : s = t) ▸ hs
  haveI : FiniteDimensional ℂ (fixd π ((glIwa k n).I1 c)) := by
    have hfix : fixd π ((glIwa k n).I1 c) = fixed π ((glIwa k n).I1 c) := by
      ext v
      exact ⟨fun h u => by simpa using h u u.2, fun h u hu => by simpa using h ⟨u, hu⟩⟩
    rw [hfix]
    exact ((H.loc.bz k).1 _ V π hπ hirr).2 _ (hI c).1 (hI c).2
  let p : V →ₗ[ℂ] Jacquet π (unipB k (Fin n)) := Submodule.mkQ _
  have hinj : ∀ v ∈ invPart π c φ, p v = 0 → v = 0 := fun v hv h =>
    OrdB.inv_inj _ π c φ hφ (hsm hπ) hv (hker ▸ (Submodule.Quotient.mk_eq_zero _).1 h)
  have heig : invPart π c φ ≤ (glIwa k n).eig π c φ := fun v hv => by simpa using (Submodule.mem_iInf _).1 hv 0
  have hp : ∀ t v, jacB π t (p v) =
      (((deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) t))⁻¹ : ℂˣ) : ℂ) • p (π (diagT k (Fin n) t) v) :=
    fun t v => UnramFixed.jacB_apply π t _
  let E : Submodule ℂ (Jacquet π (unipB k (Fin n))) :=
    ⨅ (i : Fin n) (u : Uo k), Module.End.eigenspace (jacB π (Pi.mulSingle i (u : kˣ))) (((φ (eT k n i u))⁻¹ : ℂˣ) : ℂ)
  have hE : ∀ y, y ∈ E ↔ ∀ (i : Fin n) (u : Uo k),
      jacB π (Pi.mulSingle i (u : kˣ)) y = (((φ (eT k n i u))⁻¹ : ℂˣ) : ℂ) • y := fun y => by
    simp only [E, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  have hEs : ∀ t, ∀ y ∈ E, jacB π t y ∈ E := fun t y hy => (hE _).2 fun i u => by
    rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply, (hE _).1 hy, map_smul]
  have hpE : ∀ v ∈ invPart π c φ, p v ∈ E := fun v hv => (hE _).2 fun i u => by
    have hO : (Pi.mulSingle i (u : kˣ) : Fin n → kˣ) ∈ torusO k (Fin n) := fun j => by
      by_cases h : j = i
      · subst h
        rw [Pi.mulSingle_eq_same]; exact u.2
      · simp [Pi.mulSingle_eq_of_ne h]
    rw [hp, UnramFixed.deltaHalf_torusO k hO, inv_one, Units.val_one, one_smul, ← map_smul]
    exact congrArg p ((heig hv).2.2 (eT k n i u))
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hl : HasFiniteLength (jacB π) :=
    (hasFiniteLength_comp_iff _ _ (leviTorus k (Fin n)).surjective).2
      ((H.loc.bz k).2.1 _ _ _ (points (Fin n)) _ π hπ (hasFiniteLength_of_isIrreducible hirr))
  haveI := GlobalTheory.TorusEigenform.secondCountableTopology_units k
  obtain ⟨μ, hμs, hμ, l, hl0, hle⟩ := OrdB.exists_form (isSmooth_jacB hπ) hl fun h => hx0 (hinj x hx h)
  obtain ⟨ψ, hψ, rfl⟩ : ∃ ψ : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ torusChar ψ = μ := by
    refine ⟨fun i => μ.comp (MonoidHom.mulSingle (fun _ => kˣ) i),
      fun i => hμs.comp _ (continuous_mulSingle (A := fun _ => kˣ) i), MonoidHom.ext fun t => ?_⟩
    rw [torusChar_apply]
    conv_rhs => rw [← Finset.univ_prod_mulSingle t, map_prod]
    rfl
  have hsq : IsSubquotient π (prinSeries ψ) := GlobalTheory.SatakeExists.isSubquotient_of_eigenform hπ hirr _ l hl0 hle
  have hψφ : ∀ i (u : Uo k), ψ i u = (φ (eT k n i u))⁻¹ := fun i u => by
    rw [← OrdB.tc_single]
    exact Units.ext (hμ _ _ ((hE _).1 (hpE x hx) i u))
  obtain ⟨hfd, -, hmult⟩ := UpperTheory.V.AlgebraTools.jqMult H.loc.geo H.loc.bz k n V π ψ hπ hψ hsq
  have hw : ∀ w : Equiv.Perm (Fin n), (∀ i (u : Uo k), ψ (w i) u = ψ i u) → w = 1 := fun w h => by
    refine Equiv.ext fun i => by_contra fun hi => ?_
    obtain ⟨u, hu⟩ := hD _ _ hi
    exact hu (inv_injective ((hψφ _ u).symm.trans ((h i u).trans (hψφ i u))))
  have hgen : E ≤ ⨅ t, Module.End.maxGenEigenspace (jacB π t) (torusChar ψ t : ℂ) := by
    refine le_iInf (OrdB.le_gen _ E hEs _ fun χ y hy hy0 hχ => ?_)
    have h1 : (⨅ t, Module.End.maxGenEigenspace (jacB π t) (χ t : ℂ) : Submodule ℂ _) ≠ ⊥ :=
      (Submodule.ne_bot_iff _).2 ⟨y, (Submodule.mem_iInf _).2 fun t =>
        (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨1, by rw [OrdB.pow_eig (hχ t)]; simp⟩, hy0⟩
    have h2 := (Nat.pos_of_ne_zero fun h => h1 (Submodule.finrank_eq_zero.1 h)).trans_le (hmult χ)
    obtain ⟨⟨w, rfl⟩⟩ := (Nat.card_pos_iff.1 h2).1
    rw [hw w fun i u => ?_]
    · rfl
    have h3 := (hχ _).symm.trans ((hE _).1 hy i u)
    rw [OrdB.tc_single, ← hψφ] at h3
    exact Units.ext (smul_left_injective ℂ hy0 h3)
  have hE1 : Module.finrank ℂ E ≤ 1 := by
    refine (Submodule.finrank_mono hgen).trans ((hmult _).trans ?_)
    have key : ∀ a : {w : Equiv.Perm (Fin n) // torusChar ψ = torusChar (ψ ∘ w)}, a.1 = 1 := fun a =>
      hw _ fun i u => by
        have := DFunLike.congr_fun a.2 (Pi.mulSingle i (u : kˣ))
        rw [OrdB.tc_single, OrdB.tc_single] at this
        exact this.symm
    exact Finite.card_le_one_iff_subsingleton.2 ⟨fun a b => Subtype.ext ((key a).trans (key b).symm)⟩
  have hact : ∀ t, ∀ y ∈ E, jacB π t y = (torusChar ψ t : ℂ) • y := fun t y hy => by
    by_cases hy0 : y = 0
    · simp [hy0]
    have hy1 : (⟨y, hy⟩ : E) ≠ 0 := fun h => hy0 (congrArg Subtype.val h)
    have : Nontrivial E := nontrivial_of_ne _ _ hy1
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hy1).1 (le_antisymm hE1 Module.finrank_pos) ⟨_, hEs t y hy⟩
    have ha' : jacB π t y = a • y := (congrArg Subtype.val ha).symm
    rw [ha', OrdB.eq_of_gen ha' hy0 ((Submodule.mem_iInf _).1 (hgen hy) t)]
  obtain ⟨ω, rfl⟩ : ∃ ω : Fin n → kˣ →* ℂˣ, (fun i => ω i * absPow k (((n : ℂ) - 1) / 2)) = ψ :=
    ⟨fun i => ψ i * (absPow k (((n : ℂ) - 1) / 2))⁻¹, funext fun i => inv_mul_cancel_right _ _⟩
  have hω : ∀ i, IsSmoothChar (ω i) := fun i => by
    have := (hψ i).mul (isSmoothChar_of_isUnram (isUnram_absPow k (-(((n : ℂ) - 1) / 2))))
    rwa [absPow_neg, mul_inv_cancel_right] at this
  have hinv : IsInvOn φ ω := fun i u => by
    have := hψφ i u
    rw [MonoidHom.mul_apply, isUnram_absPow k _ _ u.2, mul_one] at this
    rw [this, inv_inv]
  refine ⟨ω, hω, hinv, (_root_.UpperTheory.V.Hi.prin_series_irreducible_and_unique_subquotient H k n ω hω fun i j hij => ?_).2 V π hirr hsq, le_antisymm ?_ ?_, fun v hv j hj => ?_⟩
  · obtain ⟨u, hu⟩ := hD i j hij
    rw [hinv, hinv] at hu
    refine ⟨fun h => hu (by rw [h]), fun h => hu ?_⟩
    rw [h, MonoidHom.mul_apply, isUnram_absPow k _ _ u.2, mul_one]
  · refine le_trans (LinearMap.finrank_le_finrank_of_injective (f := p.restrict hpE) ?_) hE1
    exact (injective_iff_map_eq_zero _).2 fun v h => Subtype.ext (hinj v v.2 (congrArg Subtype.val h))
  · haveI : FiniteDimensional ℂ (invPart π c φ) :=
      Submodule.finiteDimensional_of_le (heig.trans (OrdB.eig_le _ π c φ hφ))
    exact Nat.pos_of_ne_zero fun h => hne (Submodule.finrank_eq_zero.1 h)
  · rw [← sub_eq_zero]
    refine hinj _ (sub_mem (OrdB.inv_stab _ π c φ hφ (al_mem k n j) hv) (Submodule.smul_mem _ _ hv)) ?_
    have h1 := propCp _ (glIwa k n) ℂ V π _ (al_mem k n j) v (heig hv).1
    rw [hker, hidx j hj] at h1
    have h2 : p _ = 0 := (Submodule.Quotient.mk_eq_zero _).2 h1
    have h3 := (hp (fun i => unif k ^ (if (i : ℕ) < j then 1 else 0 : ℤ)) v).symm.trans (hact _ _ (hpE v hv))
    rw [← Units.smul_def, inv_smul_eq_iff, Units.smul_def, smul_smul] at h3
    rw [map_sub, map_smul, sub_eq_zero] at h2 ⊢
    rw [h2, ← OrdB.num ω hj, mul_smul, ← h3]
    rfl
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
section General
open UpperTheory.V.Hi Polynomial
private theorem onto_inf {M : Type} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) (Y S : Submodule ℂ M)
    [FiniteDimensional ℂ S] (hS : S.map T = S) (hY : ∀ F ∈ Y ⊓ S, T F ∈ Y) :
    ∀ F ∈ Y ⊓ S, ∃ F' ∈ Y ⊓ S, T F' = F := by
  have h1 : ∀ F ∈ S, T F ∈ S := fun F hF => hS ▸ Submodule.mem_map_of_mem hF
  have h2 : ∀ F ∈ Y ⊓ S, T F ∈ Y ⊓ S := fun F hF => ⟨hY F hF, h1 F hF.2⟩
  have inj : Function.Injective (T.restrict h1) := by
    refine LinearMap.injective_iff_surjective.2 fun y => ?_
    obtain ⟨z, hz, e⟩ : (y : M) ∈ S.map T := hS.symm ▸ y.2
    exact ⟨⟨z, hz⟩, Subtype.ext e⟩
  haveI : FiniteDimensional ℂ (Y ⊓ S : Submodule ℂ M) := Submodule.finiteDimensional_of_le inf_le_right
  have sur : Function.Surjective (T.restrict h2) := by
    refine LinearMap.injective_iff_surjective.1 fun a b e => Subtype.ext ?_
    have : T.restrict h1 ⟨a, a.2.2⟩ = T.restrict h1 ⟨b, b.2.2⟩ := Subtype.ext (Subtype.ext_iff.1 e :)
    exact (Subtype.ext_iff.1 (inj this) :)
  intro F hF
  obtain ⟨z, e⟩ := sur ⟨F, hF⟩
  exact ⟨z, z.2, congrArg Subtype.val e⟩
private theorem kill_poly {A N : Type} [CommRing A] [AddCommGroup N] [Module A N] [Module.Finite A N]
    (U : Module.End A N) (hU : Function.Surjective U) : ∃ q : A[X], aeval U (1 + X * q) = 0 := by
  obtain ⟨r, hr, h0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul (Ideal.span {(X : A[X])})
    (⊤ : Submodule A[X] (Module.AEval' U)) Module.Finite.fg_top (fun y _ => by
      obtain ⟨z, hz⟩ := hU ((Module.AEval'.of U).symm y)
      have : y = (X : A[X]) • Module.AEval'.of U z := by
        rw [Module.AEval'.X_smul_of, hz, LinearEquiv.apply_symm_apply]
      rw [this]
      exact Submodule.smul_mem_smul (Ideal.subset_span rfl) trivial)
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.1 hr
  refine ⟨q, LinearMap.ext fun y => ?_⟩
  have := h0 (Module.AEval'.of U y) trivial
  rw [show r = 1 + X * q by rw [← hq]; ring, ← Module.AEval.of_aeval_smul] at this
  exact (LinearEquiv.map_eq_zero_iff _).1 this
private theorem unit_eig {A N M κ : Type} [CommRing A] [AddCommGroup N] [Module A N] [Module.Finite A N]
    [AddCommGroup M] [Module ℂ M] [NormedField κ] [IsUltrametricDist κ] (ι : κ ≃+* ℂ) (x : A →+* κ)
    (hx : ∀ a, ‖x a‖ ≤ 1) (U : Module.End A N) (hU : Function.Surjective U) (T : Module.End ℂ M)
    (s : N →ₛₗ[ι.toRingHom.comp x] M) (hs : ∀ f, s (U f) = T (s f)) {F : M}
    (hF : F ∈ Submodule.span ℂ (Set.range s)) (h0 : F ≠ 0) {μ : ℂ} (hμ : T F = μ • F) (hle : ‖ι.symm μ‖ ≤ 1) :
    ‖ι.symm μ‖ = 1 := by
  obtain ⟨q, hq⟩ := kill_poly U hU
  have hpow : ∀ (k : ℕ) f, s ((U ^ k) f) = (T ^ k) (s f) := fun k => by
    induction k with
    | zero => exact fun _ => rfl
    | succ k ih => intro f; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hs]
  have hpol : ∀ (p : A[X]) f, s (aeval U p f) = aeval T (p.map (ι.toRingHom.comp x)) (s f) := fun p f => by
    induction p using Polynomial.induction_on' with
    | add a b ha hb => simp only [map_add, Polynomial.map_add, LinearMap.add_apply, ha, hb]
    | monomial k a =>
      rw [map_monomial, aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
        Module.algebraMap_end_apply, Module.algebraMap_end_apply, s.map_smulₛₗ, hpow]
  have hker : Submodule.span ℂ (Set.range s) ≤ LinearMap.ker (aeval T ((1 + X * q).map (ι.toRingHom.comp x))) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, ← hpol, hq, LinearMap.zero_apply, map_zero]
  have h1 := hker hF
  rw [LinearMap.mem_ker, Module.End.aeval_apply_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 hμ, h0⟩,
    smul_eq_zero_iff_left h0, eval_map] at h1
  have h2 : (1 + X * q).eval₂ x (ι.symm μ) = 0 := by
    apply ι.injective
    have := hom_eval₂ (1 + X * q) x ι.toRingHom (ι.symm μ)
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply] at this h1
    rw [this, h1, map_zero]
  have hb : ∀ p : A[X], ‖p.eval₂ x (ι.symm μ)‖ ≤ 1 := fun p => by
    induction p using Polynomial.induction_on' with
    | add a b ha hb => rw [eval₂_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
    | monomial k a =>
      rw [eval₂_monomial, norm_mul, norm_pow]
      exact mul_le_one₀ (hx a) (by positivity) (pow_le_one₀ (norm_nonneg _) hle)
  rw [eval₂_add, eval₂_one, eval₂_mul, eval₂_X, add_eq_zero_iff_neg_eq] at h2
  have h3 := congrArg norm h2
  rw [norm_neg, norm_one, norm_mul] at h3
  refine le_antisymm hle ?_
  nlinarith [hb q, norm_nonneg (ι.symm μ), norm_nonneg (q.eval₂ x (ι.symm μ))]
private theorem char_of_scalar {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)
    (E : Submodule ℂ M) {F₀ : M} (h₀ : F₀ ∈ E) (hne : F₀ ≠ 0) (h : ∀ t, ∃ a : ℂ, ∀ F ∈ E, ρ t F = a • F) :
    ∃ φ : G →* ℂˣ, ∀ t, ∀ F ∈ E, ρ t F = (((φ t)⁻¹ : ℂˣ) : ℂ) • F := by
  choose a ha using h
  let χ : G →* ℂ :=
    { toFun := a
      map_one' := smul_left_injective ℂ hne (by simpa using (ha 1 F₀ h₀).symm)
      map_mul' := fun s t => smul_left_injective ℂ hne (by
        have := ha (s * t) F₀ h₀
        rw [map_mul, Module.End.mul_apply, ha t F₀ h₀, map_smul, ha s F₀ h₀, smul_smul, mul_comm] at this
        exact this.symm) }
  exact ⟨χ.toHomUnits⁻¹, fun t F hF => by simpa [χ] using ha t F hF⟩
private theorem uOp_factor {σ : Type} [Finite σ] [DecidableEq σ] {G : σ → Type} [∀ v, Group (G v)] (I : ∀ v, Iwa (G v))
    {M : Type} [AddCommGroup M] [Module ℂ M] (π : Representation ℂ (∀ v, G v) M) (v : σ) {a : G v} (ha : a ∈ (I v).P) :
    Pi.mulSingle v a ∈ (piIwa I).P ∧ ∀ F ∈ fixd π (piIwa I).N,
      (piIwa I).uOp π (Pi.mulSingle v a) F = (I v).uOp (π.comp (MonoidHom.mulSingle G v)) a F := by
  classical
  have hP : Pi.mulSingle v a ∈ (piIwa I).P := fun w _ => by
    rcases eq_or_ne w v with rfl | h
    · simpa using ha
    · simpa [Pi.mulSingle_eq_of_ne h] using (I w).P.one_mem
  have hN : ∀ u ∈ (I v).N, Pi.mulSingle v u ∈ (piIwa I).N := fun u hu => (Subgroup.mulSingle_mem_pi _ _).2 fun _ => hu
  have hc : ∀ {H : Type} [Group H] (J : Iwa H) (b y : H), y ∈ J.Nconj b ↔ b⁻¹ * y * b ∈ J.N := fun J b y =>
    ⟨by rintro ⟨z, hz, rfl⟩; simpa [mul_assoc] using hz, fun h => ⟨_, h, by simp [mul_assoc]⟩⟩
  refine ⟨hP, fun F hF => ?_⟩
  obtain ⟨⟨s, hs, hs'⟩, hsum⟩ := uOpSum _ (I v) ℂ M (π.comp (MonoidHom.mulSingle G v)) a ha
  have key : ∀ y ∈ (piIwa I).N, ∀ u : G v, (Pi.mulSingle v u)⁻¹ * y ∈ (piIwa I).Nconj (Pi.mulSingle v a) ↔
      u⁻¹ * y v ∈ (I v).Nconj a := fun y hy u => by
    rw [hc, hc]
    refine ⟨fun h => by simpa using h v trivial, fun h w _ => ?_⟩
    rcases eq_or_ne w v with rfl | e
    · simpa using h
    · simpa [Pi.mulSingle_eq_of_ne e] using hy w trivial
  rw [(hsum s hs hs').2 F fun u hu => hF _ (hN u hu),
    ((uOpSum _ (piIwa I) ℂ M π _ hP).2 (s.image (Pi.mulSingle v)) ?_ ?_).2 F hF,
    Finset.sum_image fun _ _ _ _ e => Pi.mulSingle_injective v e]
  · exact Finset.sum_congr rfl fun u _ => by rw [← Pi.mulSingle_mul]; rfl
  · intro u hu
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hu
    exact hN w (hs w hw)
  · intro y hy
    obtain ⟨u, ⟨hu, hu'⟩, huq⟩ := hs' (y v) (hy v trivial)
    refine ⟨_, ⟨Finset.mem_image_of_mem _ hu, (key y hy u).2 hu'⟩, ?_⟩
    rintro _ ⟨hw, hw'⟩
    obtain ⟨w, hw₁, rfl⟩ := Finset.mem_image.1 hw
    rw [huq w ⟨hw₁, (key y hy w).1 hw'⟩]
variable {G M : Type} [Group G] (I : Iwa G) [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)
private theorem uOp_stable {Y : Submodule ℂ M} (hY : ∀ g, ∀ F ∈ Y, ρ g F ∈ Y) {a : G} (ha : a ∈ I.P) {F : M}
    (hF : F ∈ Y) (hN : F ∈ fixd ρ I.N) : I.uOp ρ a F ∈ Y := by
  obtain ⟨⟨s, hs, hs'⟩, hsum⟩ := uOpSum _ I ℂ M ρ a ha
  rw [(hsum s hs hs').2 F hN]
  exact Y.sum_mem fun u _ => hY _ F hF
private theorem onto_prod {E : Submodule ℂ M} (hE : E ≤ fixd ρ I.N) (s : List G)
    (h : ∀ a ∈ s, a ∈ I.P ∧ ∀ F ∈ E, ∃ F' ∈ E, I.uOp ρ a F' = F) :
    s.prod ∈ I.P ∧ ∀ F ∈ E, ∃ F' ∈ E, I.uOp ρ s.prod F' = F := by
  induction s with
  | nil => exact ⟨I.P.one_mem, fun F hF => ⟨F, hF, (uOpMul _ I ℂ M ρ 1 1 I.P.one_mem I.P.one_mem F (hE hF)).2.2.1⟩⟩
  | cons a s ih =>
    obtain ⟨h1, h2⟩ := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    obtain ⟨h3, h4⟩ := h a List.mem_cons_self
    refine ⟨by rw [List.prod_cons]; exact I.P.mul_mem h3 h1, fun F hF => ?_⟩
    obtain ⟨F₁, m₁, e₁⟩ := h4 F hF
    obtain ⟨F₂, m₂, e₂⟩ := h2 F₁ m₁
    exact ⟨F₂, m₂, by rw [List.prod_cons, ← (uOpMul _ I ℂ M ρ a _ h3 h1 F₂ (hE m₂)).2.1, e₂, e₁]⟩
private theorem into_inv {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) {Y E : Submodule ℂ M}
    (hEY : E ≤ Y) (c : ℕ) (φ : I.T →* ℂˣ) (hE : E ≤ I.eig ρ c φ) (hz : ∀ F ∈ E, ∃ F' ∈ E, I.uOp ρ I.z F' = F)
    (p : M →ₗ[ℂ] V) (hp : ∀ g, ∀ y ∈ Y, p (ρ g y) = π g (p y)) {F : M} (hF : F ∈ E) :
    p F ∈ ⨅ j : ℕ, (I.eig π c φ).map (I.uOp π I.z ^ j) := by
  refine (Submodule.mem_iInf _).2 fun j => ?_
  induction j generalizing F with
  | zero =>
    obtain ⟨h1, h2, h3⟩ := hE hF
    exact ⟨p F, ⟨fun u hu => by rw [← hp u F (hEY hF), h1 u hu], fun u hu => by rw [← hp u F (hEY hF), h2 u hu],
      fun t => by rw [← hp t F (hEY hF), h3 t, map_smul]⟩, rfl⟩
  | succ j ih =>
    obtain ⟨F', m, rfl⟩ := hz F hF
    obtain ⟨w, hw, e⟩ := ih m
    refine ⟨w, hw, ?_⟩
    rw [pow_succ', Module.End.mul_apply, e]
    exact (uOpNat _ I ℂ M ρ ℂ V π p.toAddMonoidHom _ I.z_mem F' fun u _ => hp _ F' (hEY m)).symm
end General
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance high] UpperTheory.V.W.coefLocal
private theorem Uc_anti (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : ℕ} (h : a ≤ b) : Uc k b ≤ Uc k a := by
  refine Subgroup.map_mono fun u hu => ?_
  rw [MonoidHom.mem_ker, Units.ext_iff] at hu ⊢
  exact (Ideal.Quotient.eq (y := 1)).2 (Ideal.pow_le_pow_right h ((Ideal.Quotient.eq (y := 1)).1 hu))
private theorem al_zero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) : al k n 0 = 1 := by
  rw [al, upow, ← (diagT k (Fin n)).map_one]
  congr 1
  funext i
  simp
private theorem local_step (hLit : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
    (ρ : Representation ℂ (GL (Fin n) k) M) {Y E : Submodule ℂ M} (σ : SmIrr (GL (Fin n) k)) (hσ : IsoSum ρ Y σ)
    (hY : ∀ g, ∀ F ∈ Y, ρ g F ∈ Y) (hEY : E ≤ Y) {F₀ : M} (hF₀ : F₀ ∈ E) (hF₀' : F₀ ≠ 0) (e : ℕ)
    (f : Fin n → Uo k → ℂ) (hN : E ≤ fixd ρ (glIwa k n).N) (hNm : E ≤ fixd ρ ((glIwa k n).Nm e))
    (hT : ∀ i y, ∀ F ∈ E, ρ (eT k n i y) F = (f i y)⁻¹ • F)
    (htriv : ∀ i (y : Uo k), (y : kˣ) ∈ Uc k (e + 1) → f i y = 1) (hdis : ∀ i j, i ≠ j → ∃ y, f i y ≠ f j y)
    (honto : ∀ j : Fin n, ∀ F ∈ E, ∃ F' ∈ E, (glIwa k n).uOp ρ (al k n (j + 1)) F' = F) :
    ∃ ω : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) ∧ Nonempty (σ.ρ.Equiv (PS ω)) ∧
      (∀ i (y : Uo k), (ω i y : ℂ) * f i y = 1) ∧
      ∀ j ≤ n, ∀ F ∈ E, (glIwa k n).uOp ρ (al k n j) F = psEig ω j • F := by
  obtain ⟨-, -, -, -, -, -, -, -, hz, hgen⟩ := glBridge k n M ρ
  obtain ⟨φ, hφ⟩ := char_of_scalar (ρ.comp (glIwa k n).T.subtype) E hF₀ hF₀' fun t => by
    obtain ⟨y, hy, -⟩ := hgen t
    change ∃ a : ℂ, ∀ F ∈ E, ρ t F = a • F
    rw [hy]
    refine List.prod_induction (fun g => ∃ a : ℂ, ∀ F ∈ E, ρ g F = a • F) ?_ ⟨1, by simp⟩ ?_
    · rintro g g' ⟨a, ha⟩ ⟨b, hb⟩
      exact ⟨b * a, fun F hF => by rw [map_mul, Module.End.mul_apply, hb F hF, map_smul, ha F hF, smul_smul]⟩
    · intro g hg
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
      exact ⟨_, hT i (y i)⟩
  have hval : ∀ i y, (φ (eT k n i y) : ℂ) = f i y := fun i y => by
    have := smul_left_injective ℂ hF₀' ((hφ (eT k n i y) F₀ hF₀).symm.trans (hT i y F₀ hF₀))
    rwa [Units.val_inv_eq_inv_val, inv_inj] at this
  have hzo : ∀ F ∈ E, ∃ F' ∈ E, (glIwa k n).uOp ρ (glIwa k n).z F' = F := by
    rw [hz]
    refine (onto_prod _ _ hN _ fun a ha => ?_).2
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ha
    refine ⟨al_mem k n j, ?_⟩
    rcases j with _ | j
    · rw [al_zero]
      exact fun F hF => ⟨F, hF, (uOpMul _ _ ℂ _ _ 1 1 (one_mem _) (one_mem _) F (hN hF)).2.2.1⟩
    · exact honto ⟨j, by have := List.mem_range.1 hj; omega⟩
  have hinv : ∀ p : M →ₗ[ℂ] σ.V, (∀ g, ∀ y ∈ Y, p (ρ g y) = σ.ρ g (p y)) → ∀ F ∈ E, p F ∈ invPart σ.ρ e φ :=
    fun p hp F hF => into_inv (glIwa k n) ρ σ.ρ hEY e φ (fun F hF => ⟨hN hF, hNm hF, fun t => hφ t F hF⟩) hzo p hp hF
  obtain ⟨p₀, hp₀, hp₀'⟩ := isoSep hσ (hEY hF₀) hF₀'
  obtain ⟨ω, h1, h2, h3, -, h4⟩ := _root_.UpperTheory.V.Hi.exists_principal_series_of_distinct_inv_ne_bot hLit k n _ σ.ρ σ.smooth σ.irred e φ
    (fun i y hy => Units.ext (by rw [hval, htriv i y hy, Units.val_one]))
    (fun i j hij => by
      obtain ⟨y, hy⟩ := hdis i j hij
      exact ⟨y, fun h => hy (by rw [← hval, ← hval, h])⟩)
    ((Submodule.ne_bot_iff _).2 ⟨_, hinv p₀ hp₀ F₀ hF₀, hp₀'⟩)
  refine ⟨ω, h1, h3, fun i y => by rw [← hval, h2 i y, Units.mul_inv], fun j hj F hF => ?_⟩
  by_contra hc
  obtain ⟨p, hp, hp'⟩ := isoSep hσ (sub_mem (uOp_stable _ _ hY (al_mem k n j) (hEY hF) (hN hF))
    (Y.smul_mem (psEig ω j) (hEY hF))) (sub_ne_zero.2 hc)
  refine hp' ?_
  rw [map_sub, map_smul, ← h4 _ (hinv p hp F hF) j hj, sub_eq_zero]
  exact uOpNat _ _ ℂ _ _ ℂ _ σ.ρ p.toAddMonoidHom _ (al_mem k n j) F fun u _ => hp _ F (hEY hF)
theorem UpperTheory.V.Hi.goodScalB_alt : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis →
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
      (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ)
      (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d), H.IsSpec θ ι x.toRingHom lam ξ c0 sp → H.Good θ x.toRingHom lam →
    ∀ (Y : H.PartAltAlt ι lam ξ) (K : H.Lev) (e : ℕ), c0 ≤ e → Y.Y ⊓ H.OrdAt θ ι x.toRingHom lam ξ K e ≠ ⊥ →
      ∃ ω : ∀ v : H.V, Fin n → ((H.Sl v).adicCompletion L)ˣ →* ℂˣ,
        (∀ v i, IsSmoothChar (ω v i)) ∧ (∀ v, Nonempty ((Y.σl v).ρ.Equiv (PS (ω v)))) ∧
        (∀ v i (y : Uo ((H.Sl v).adicCompletion L)), (ω v i y : ℂ) * ι (H.finPart θ x.toRingHom lam v i y) = 1) ∧
        ∀ (v : H.V) (j : Fin n), ‖ι.symm ((H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1))‖ = 1 ∧
          ∀ F ∈ Y.Y ⊓ H.OrdAt θ ι x.toRingHom lam ξ K e,
            H.opC ι lam d (.inr (v, j)) F = ((H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1)) • F := by
  intro hLit L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι x lam d ξ c0 sp hsp hgood Y K e he hne
  classical
  haveI : Finite (ResidueField c.O) := Module.finite_of_finite (ResidueField ℤ_[l])
  haveI : IsCNL A := IsCNL.ofCO c.O A
  set S := H.OrdAt θ ι x.toRingHom lam ξ K e with hSdef
  have hSC : S ≤ H.ClAt θ ι x.toRingHom lam ξ K e := iSup_le fun _ => inf_le_left
  haveI := hsp.fin K e he
  haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hSC
  obtain ⟨F₀, hF₀, hF₀'⟩ := (Submodule.ne_bot_iff _).1 hne
  obtain ⟨hfin, -, hbij⟩ := ordFree _ _ _ H.X A H.m (H.τA A) θ hθ.cont (H.lev K) (hH.fin K) (hθ.free K)
  let s : H.X.Ord (H.τA A) θ (H.lev K) →ₛₗ[ι.toRingHom.comp x.toRingHom] (Fin H.m → H.X.Fn ℂ d) :=
    { toFun := fun f => sp f
      map_add' := fun f g => hsp.add K f f.2 g g.2
      map_smul' := fun b f => hsp.smul K f f.2 b }
  have hspan : Submodule.span ℂ (Set.range s) = S := by
    rw [hSdef, ← hsp.span K e he, Set.image_eq_range]
    rfl
  have hfac := fun (v : H.V) (j : ℕ) => uOp_factor (fun v : H.V => glIwa ((H.Sl v).adicCompletion L) n)
    (H.X.rpF ℂ d H.m) v (al_mem _ n j)
  have hbij' := fun (v : H.V) (j : Fin n) => hbij (alV n H.Sl v (j + 1)) (hfac v (j + 1)).1
  let U : H.V → Fin n → Module.End A (H.X.Ord (H.τA A) θ (H.lev K)) := fun v j =>
    (H.op A (.inr (v, j))).restrict (hbij' v j).mapsTo
  have hU : ∀ v j, Function.Surjective (U v j) := fun v j y => by
    obtain ⟨z, hz, ez⟩ := (hbij' v j).surjOn y.2
    exact ⟨⟨z, hz⟩, Subtype.ext ez⟩
  have hsU : ∀ v j f, s (U v j f) = H.opC ι lam d (.inr (v, j)) (s f) := fun v j f => hsp.op K _ f f.2
  have hSmap : ∀ v j, S.map (H.opC ι lam d (.inr (v, j))) = S := fun v j => by
    rw [← hspan, Submodule.map_span, ← Set.range_comp, ← (hU v j).range_comp s]
    exact congrArg (fun t => Submodule.span ℂ (Set.range t)) (funext fun f => (hsU v j f).symm)
  have hY : ∀ v g, ∀ F ∈ Y.Y, H.atV d v g F ∈ Y.Y := fun v g F hF => by
    refine (iSup_le ?_ : _ ≤ Y.Y.comap (H.atV d v g)) (Y.isoL v hF)
    rintro f _ ⟨w, rfl⟩
    exact f.2.2 ⟨_, f.2.1 g w⟩
  have hN : ∀ v, Y.Y ⊓ S ≤ fixd (H.atV d v) (glIwa _ n).N := fun v F hF u hu =>
    (hSC hF.2).1.1.2 _ ((Subgroup.mulSingle_mem_pi _ _).2 fun _ => hu)
  have hNm : ∀ v, Y.Y ⊓ S ≤ fixd (H.atV d v) ((glIwa _ n).Nm e) := fun v F hF u hu =>
    (hSC hF.2).1.2 _ ((Subgroup.mulSingle_mem_pi _ _).2 fun _ => hu)
  have hT : ∀ v i y, ∀ F ∈ Y.Y ⊓ S,
      H.atV d v (eT _ n i y) F = (ι (H.finPart θ x.toRingHom lam v i y))⁻¹ • F := fun v i y F hF => by
    have := (hSC hF.2).2
    simp only [SetLike.mem_coe, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at this
    exact this v i y
  have hop : ∀ v (j : Fin n), ∀ F ∈ Y.Y ⊓ S, H.opC ι lam d (.inr (v, j)) F =
      (H.lowVal ι lam v (j + 1))⁻¹ • (glIwa _ n).uOp (H.atV d v) (al _ n (j + 1)) F := fun v j F hF =>
    congrArg ((H.lowVal ι lam v (j + 1))⁻¹ • ·) ((hfac v (j + 1)).2 F (hSC hF.2).1.1.2)
  have honto : ∀ v (j : Fin n), ∀ F ∈ Y.Y ⊓ S, ∃ F' ∈ Y.Y ⊓ S,
      (glIwa _ n).uOp (H.atV d v) (al _ n (j + 1)) F' = F := fun v j F hF => by
    obtain ⟨F', m, e'⟩ := onto_inf _ Y.Y S (hSmap v j) (fun F hF => by
      rw [hop v j F hF]
      exact Y.Y.smul_mem _ (uOp_stable _ _ (hY v) (al_mem _ n _) hF.1 (hN v hF))) F hF
    rw [hop v j F' m, ← map_smul] at e'
    exact ⟨_, Submodule.smul_mem _ _ m, e'⟩
  have loc := fun v => local_step hLit (H.atV d v) (Y.σl v) (Y.isoL v) (hY v) inf_le_left hF₀ hF₀' e
    (fun i y => ι (H.finPart θ x.toRingHom lam v i y)) (hN v) (hNm v) (hT v)
    (fun i y hy => by rw [hsp.triv v i y (Uc_anti _ (by omega) hy), map_one])
    (fun i j hij => (hgood.2.2 v i j hij).imp fun y hy h => hy (ι.injective h)) (honto v)
  choose ω h1 h2 h3 h4 using loc
  have heig : ∀ v (j : Fin n), ∀ F ∈ Y.Y ⊓ S, H.opC ι lam d (.inr (v, j)) F =
      ((H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1)) • F := fun v j F hF => by
    rw [hop v j F hF, h4 v (j + 1) j.2 F hF, smul_smul]
  obtain ⟨-, a, -, -, ha⟩ := (UpperTheory.V.GradeZeroInterpolatingElement.coPt c A).1 x
  exact ⟨ω, h1, h2, h3, fun v j => ⟨unit_eig ι x.toRingHom (fun b => by simpa using ha 0 b (by simp)) (U v j) (hU v j) _ s
    (hsU v j) (hspan.symm ▸ hF₀.2) hF₀' (heig v j F₀ hF₀)
    (hsp.int K e he _ F₀ (hSC hF₀.2) hF₀' _ (heig v j F₀ hF₀)), heig v j⟩⟩
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
section Abs
open TensorProduct
universe u
variable {A K M W ι : Type} [CommRing A] [Field K] [Algebra A K] [AddCommGroup M] [Module A M]
  [AddCommGroup W] [Module K W] [Module A W] [IsScalarTower A K W]
private theorem pa_rho {N : Type} [AddCommGroup N] [Module A N] (s : N →ₗ[A] W)
    (hs : Function.Injective (s.liftBaseChange K)) (E : Submodule K W) (hE : E = Submodule.span K (Set.range s)) :
    ∃ (ρ : Module.End A N →+* Module.End K E) (Ψ : K ⊗[A] N ≃ₗ[K] E),
      (∀ φ v, ρ φ (Ψ v) = Ψ (φ.baseChange K v)) ∧
      (∀ φ f (F : E), (F : W) = s f → (ρ φ F : W) = s (φ f)) ∧
      (∀ (b : A) F, ρ (algebraMap A _ b) F = algebraMap A K b • F) := by
  have hr : LinearMap.range (s.liftBaseChange K) = E := by
    rw [LinearMap.range_liftBaseChange, hE]; rfl
  let Ψ : K ⊗[A] N ≃ₗ[K] E := (LinearEquiv.ofInjective _ hs).trans (LinearEquiv.ofEq _ _ hr)
  have hΨ : ∀ v, (Ψ v : W) = s.liftBaseChange K v := fun v => rfl
  let ρ : Module.End A N →+* Module.End K E :=
    (Ψ.conjRingEquiv : Module.End K (K ⊗[A] N) →+* Module.End K E).comp (Module.End.baseChangeHom A K N).toRingHom
  have h1 : ∀ φ v, ρ φ (Ψ v) = Ψ (φ.baseChange K v) := fun φ v => by
    change Ψ (φ.baseChange K (Ψ.symm (Ψ v))) = _
    rw [Ψ.symm_apply_apply]
  refine ⟨ρ, Ψ, h1, fun φ f F hF => ?_, fun b F => ?_⟩
  · have : F = Ψ (1 ⊗ₜ f) := Subtype.ext (by rw [hF, hΨ]; simp)
    rw [this, h1, hΨ]; simp
  · obtain ⟨v, rfl⟩ := Ψ.surjective F
    rw [h1, ← map_smul, Algebra.algebraMap_eq_smul_one b, LinearMap.baseChange_smul, LinearMap.baseChange_one]
    simp
private theorem pa_ext {N W' : Type} [AddCommGroup N] [Module A N] [AddCommGroup W'] [Module K W'] (s : N →ₗ[A] W)
    (E : Submodule K W) (hE : E = Submodule.span K (Set.range s)) (α β : E →ₗ[K] W')
    (h : ∀ f (F : E), (F : W) = s f → α F = β F) (F : E) : α F = β F := by
  obtain ⟨F, hF⟩ := F
  subst hE
  induction hF using Submodule.span_induction with
  | mem x hx => obtain ⟨f, rfl⟩ := hx; exact h f _ rfl
  | zero => exact (map_zero α).trans (map_zero β).symm
  | add x y hx hy h1 h2 => exact ((map_add α ⟨x, hx⟩ ⟨y, hy⟩).trans (by rw [h1, h2])).trans (map_add β ⟨x, hx⟩ ⟨y, hy⟩).symm
  | smul c x hx h1 => exact ((map_smul α c ⟨x, hx⟩).trans (by rw [h1])).trans (map_smul β c ⟨x, hx⟩).symm
private theorem pa_op (Y : Submodule A M) (op : ι → Module.End A M) (s : Y →ₗ[A] W) (opC : ι → Module.End K W)
    (hop : ∀ i (f g : Y), (g : M) = op i f → s g = opC i (s f))
    (E : Submodule K W) (hE : E = Submodule.span K (Set.range s)) (ρ : Module.End A Y →+* Module.End K E)
    (h1 : ∀ φ f (F : E), (F : W) = s f → (ρ φ F : W) = s (φ f)) (i : ι) (t : Module.End A Y) (ht : Restr t (op i))
    (F : E) : (ρ t F : W) = opC i F :=
  pa_ext s E hE (E.subtype ∘ₗ ρ t) (opC i ∘ₗ E.subtype) (fun f F hF => by
    change (ρ t F : W) = opC i F
    rw [h1 t f F hF, hF, hop i f _ (ht f)]) F
private theorem pa_stab (Y : Submodule A M) (op : ι → Module.End A M) (opC : ι → Module.End K W)
    (E : Submodule K W) (ρ : Module.End A Y →+* Module.End K E)
    (h2 : ∀ i t, Restr t (op i) → ∀ F : E, (ρ t F : W) = opC i F)
    (h3 : ∀ (b : A) F, ρ (algebraMap A _ b) F = algebraMap A K b • F)
    (Z : Submodule K W) (hZ : ∀ i, ∀ F ∈ Z ⊓ E, opC i F ∈ Z) (t : Module.End A Y) (ht : t ∈ heckeAlg Y op) :
    ∀ F : E, (F : W) ∈ Z → (ρ t F : W) ∈ Z := by
  induction ht using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨i, hi⟩ := hx; intro F hF; rw [h2 i x hi]; exact hZ i _ ⟨hF, F.2⟩
  | algebraMap b => intro F hF; rw [h3]; exact Z.smul_mem _ hF
  | add x y _ _ hx hy => intro F hF; rw [map_add]; exact Z.add_mem (hx F hF) (hy F hF)
  | mul x y _ _ hx hy => intro F hF; rw [map_mul]; exact hx _ (hy F hF)
private theorem pa_eig {T E : Type} {J : Type u} [CommRing T] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (act : T →+* Module.End K E) (z : T → K) (Z : J → Submodule K E) (hZ : ⨆ j, Z j = ⊤)
    (hst : ∀ j t, ∀ F ∈ Z j, act t F ∈ Z j) (v : E) (hv : v ≠ 0) (he : ∀ t, act t v = z t • v) :
    ∃ j, ∃ F ∈ Z j, F ≠ 0 ∧ ∀ t, act t F = z t • F := by
  have hc : ∀ s t, Commute (act s) (act t) := fun s t => (Commute.all s t).map act
  obtain ⟨φ, hφ, h⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.quotOfEig (fun t => act t) hc z v hv he
  obtain ⟨j, hj⟩ : ∃ j, φ ∘ₗ (Z j).subtype ≠ 0 := by
    by_contra hn
    push Not at hn
    refine hφ (LinearMap.ker_eq_top.1 (top_le_iff.1 (hZ ▸ iSup_le fun j F hF => ?_)))
    exact LinearMap.congr_fun (hn j) ⟨F, hF⟩
  obtain ⟨F, hF, h'⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigOfQuot (fun t => (act t).restrict (hst j t))
    (fun s t => LinearMap.ext fun F => Subtype.ext (LinearMap.congr_fun (hc s t).eq F)) z _ hj (fun t F => h t F)
  exact ⟨j, F, F.2, fun h0 => hF (Subtype.ext h0), fun t => congrArg Subtype.val (h' t)⟩
private theorem pa_chr {T E : Type} [CommRing T] [AddCommGroup E] [Module K E]
    (act : T →+* Module.End K E) (Z : Submodule K E) (hZ : Z ≠ ⊥) (h : ∀ t, ∃ μ : K, ∀ F ∈ Z, act t F = μ • F) :
    ∃ z : T →+* K, ∀ t, ∀ F ∈ Z, act t F = z t • F := by
  choose z hz using h
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hZ
  have inj : ∀ a b : K, a • v = b • v → a = b := fun a b h => smul_left_injective K hv0 h
  refine ⟨⟨⟨⟨z, inj _ _ ?_⟩, fun s t => inj _ _ ?_⟩, inj _ _ ?_, fun s t => inj _ _ ?_⟩, hz⟩
  · rw [← hz _ v hv]; simp
  · change z (s * t) • v = (z s * z t) • v
    rw [← hz _ v hv, map_mul, Module.End.mul_apply, hz t v hv, map_smul, hz s v hv, smul_smul, mul_comm]
  · change z 0 • v = _
    rw [← hz _ v hv]; simp
  · change z (s + t) • v = (z s + z t) • v
    rw [← hz _ v hv, map_add, LinearMap.add_apply, hz t v hv, hz s v hv, add_smul]
private theorem pa_inst {J : Type u} (Y0 Y : Submodule A M) [Module.Finite A Y] (hle : Y ≤ Y0) (op : ι → Module.End A M)
    [hc : Fact (CommOn Y op)] (e : Module.End A Y0) (he : e ∈ heckeAlg Y0 op)
    (hi : IsIdempotentElem e) (hY : ∀ y : Y0, (y : M) ∈ Y ↔ e y = y)
    (s : Y0 →ₗ[A] W) (hs : Function.Injective (s.liftBaseChange K)) (opC : ι → Module.End K W)
    (hop : ∀ i (f g : Y0), (g : M) = op i f → s g = opC i (s f))
    (O E : Submodule K W) (hO : O = Submodule.span K (Set.range s))
    (hE : E = Submodule.span K (Set.range (s ∘ₗ Submodule.inclusion hle)))
    (Z : J → Submodule K W) (hZ : ∀ j i, ∀ F ∈ Z j, opC i F ∈ Z j) (hOZ : O = ⨆ j, Z j ⊓ O) :
    E = ⨆ j, Z j ⊓ E ∧ ∃ act : heckeAlg Y op →+* Module.End K E,
      (∀ (t : heckeAlg Y op) (f : Y) (F : E), (F : W) = s (Submodule.inclusion hle f) →
        (act t F : W) = s (Submodule.inclusion hle ((t : Module.End A Y) f))) ∧
      (∀ i (F : E), (act (heckeGen Y op i) F : W) = opC i F) ∧
      (∀ (b : A) (F : E), act (algebraMap A _ b) F = algebraMap A K b • F) ∧
      (∀ z : heckeAlg Y op →+* K, z.comp (algebraMap A _) = algebraMap A K →
        ∃ j F, F ≠ 0 ∧ F ∈ Z j ⊓ E ∧ ∀ i, opC i F = z (heckeGen Y op i) • F) ∧
      (∀ Z' : Submodule K W, Z' ⊓ E ≠ ⊥ → (∀ i, ∃ μ : K, ∀ F ∈ Z' ⊓ E, opC i F = μ • F) →
        ∃ z : heckeAlg Y op →+* K, z.comp (algebraMap A _) = algebraMap A K ∧
          ∀ t (F : E), (F : W) ∈ Z' → act t F = z t • F) := by
  have heY : ∀ y : Y0, (e y : M) ∈ Y := fun y => (hY _).2 (LinearMap.congr_fun hi.eq y)
  let r : Y0 →ₗ[A] Y := LinearMap.codRestrict _ (Y0.subtype ∘ₗ e) heY
  have hr : r ∘ₗ Submodule.inclusion hle = LinearMap.id :=
    LinearMap.ext fun y => Subtype.ext (congrArg (fun z : Y0 => (z : M)) ((hY (Submodule.inclusion hle y)).1 y.2))
  have hs' : Function.Injective ((s ∘ₗ Submodule.inclusion hle).liftBaseChange K) := by
    have h1 : (s ∘ₗ Submodule.inclusion hle).liftBaseChange K =
        s.liftBaseChange K ∘ₗ (Submodule.inclusion hle).baseChange K := by
      ext y; simp
    rw [h1, LinearMap.coe_comp]
    refine hs.comp (Function.LeftInverse.injective (g := r.baseChange K) fun v => ?_)
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hr, LinearMap.baseChange_id, LinearMap.id_apply]
  obtain ⟨ρ0, -, -, a1, a3⟩ := pa_rho s hs O hO
  obtain ⟨ρ, Ψ, b0, b1, b3⟩ := pa_rho _ hs' E hE
  have a2 := pa_op Y0 op s opC hop O hO ρ0 a1
  have b2 := pa_op Y op (s ∘ₗ Submodule.inclusion hle) opC (fun i f g h => hop i _ _ h) E hE ρ b1
  have hEO : E ≤ O := by
    rw [hE, hO]; exact Submodule.span_mono (by rintro _ ⟨f, rfl⟩; exact ⟨_, rfl⟩)
  have hfix : ∀ F : E, (ρ0 e ⟨F, hEO F.2⟩ : W) = F :=
    pa_ext _ E hE (O.subtype ∘ₗ ρ0 e ∘ₗ Submodule.inclusion hEO) E.subtype fun f F hF => by
      change (ρ0 e ⟨F, hEO F.2⟩ : W) = F
      rw [a1 e (Submodule.inclusion hle f) _ hF, hF, (hY (Submodule.inclusion hle f)).1 f.2]
      rfl
  have hin : ∀ F : O, (ρ0 e F : W) ∈ E := fun F =>
    (Submodule.Quotient.mk_eq_zero E).1 (pa_ext s O hO (E.mkQ ∘ₗ O.subtype ∘ₗ ρ0 e) 0 (fun f F hF => by
      change E.mkQ (ρ0 e F : W) = 0
      rw [a1 e f _ hF, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hE]
      exact Submodule.subset_span ⟨r f, rfl⟩) F)
  have hsum : E = ⨆ j, Z j ⊓ E := by
    refine le_antisymm (fun F hF => ?_) (iSup_le fun j => inf_le_right)
    have key : ∀ G ∈ ⨆ j, Z j ⊓ O, ∃ h : G ∈ O, (ρ0 e ⟨G, h⟩ : W) ∈ ⨆ j, Z j ⊓ E := by
      intro G hG
      induction hG using Submodule.iSup_induction' with
      | mem j G hG =>
        exact ⟨hG.2, Submodule.mem_iSup_of_mem j
          ⟨pa_stab Y0 op opC O ρ0 a2 a3 (Z j) (fun i F hF => hZ j i F hF.1) e he _ hG.1, hin _⟩⟩
      | zero => exact ⟨zero_mem _, by rw [show (⟨0, zero_mem _⟩ : O) = 0 from rfl, map_zero]; exact zero_mem _⟩
      | add x y _ _ hx hy =>
        obtain ⟨hx, hx'⟩ := hx
        obtain ⟨hy, hy'⟩ := hy
        exact ⟨add_mem hx hy, by
          rw [show (⟨x + y, add_mem hx hy⟩ : O) = ⟨x, hx⟩ + ⟨y, hy⟩ from rfl, map_add]; exact add_mem hx' hy'⟩
    obtain ⟨h, h'⟩ := key F (hOZ ▸ hEO hF)
    rwa [show (ρ0 e ⟨F, h⟩ : W) = F from hfix ⟨F, hF⟩] at h'
  let act : heckeAlg Y op →+* Module.End K E := ρ.comp (heckeAlg Y op).val.toRingHom
  have c2 : ∀ i (F : E), (act (heckeGen Y op i) F : W) = opC i F := fun i F => b2 i _ (fun _ => rfl) F
  refine ⟨hsum, act, fun t f F hF => b1 t f F hF, c2, b3, fun z hz => ?_, fun Z' h0 hsc => ?_⟩
  · haveI : FiniteDimensional K E := Module.Finite.equiv Ψ
    obtain ⟨v, hv, hv'⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.pointEig (M := Y)
      ({ z with commutes' := fun b => RingHom.congr_fun hz b } : heckeAlg Y op →ₐ[A] K)
    have htop : ⨆ j, (Z j).comap E.subtype = ⊤ := by
      apply Submodule.map_injective_of_injective E.subtype_injective
      rw [Submodule.map_iSup, Submodule.map_subtype_top]
      simp_rw [Submodule.map_comap_subtype, inf_comm E]
      exact hsum.symm
    obtain ⟨j, F, hF, hF0, hF'⟩ := pa_eig act z (fun j => (Z j).comap E.subtype) htop
      (fun j t F hF => pa_stab Y op opC E ρ b2 b3 (Z j) (fun i F hF => hZ j i F hF.1) t t.2 F hF) (Ψ v)
      (fun h => hv (Ψ.map_eq_zero_iff.1 h)) (fun t => (b0 t v).trans (by rw [← map_smul]; exact congrArg Ψ (hv' t)))
    exact ⟨j, F, fun h => hF0 (Subtype.ext h), ⟨hF, F.2⟩, fun i => by rw [← c2, hF']; rfl⟩
  · obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h0
    obtain ⟨z, hz⟩ := pa_chr act (Z'.comap E.subtype)
      ((Submodule.ne_bot_iff _).2 ⟨⟨v, hv.2⟩, hv.1, fun h => hv0 (congrArg Subtype.val h)⟩) (by
        rintro ⟨t, ht⟩
        change ∃ μ : K, ∀ F ∈ Z'.comap E.subtype, ρ t F = μ • F
        induction ht using Algebra.adjoin_induction with
        | mem x hx =>
          obtain ⟨i, hi⟩ := hx
          obtain ⟨μ, hμ⟩ := hsc i
          exact ⟨μ, fun F hF => Subtype.ext ((b2 i x hi F).trans (hμ F ⟨hF, F.2⟩))⟩
        | algebraMap b => exact ⟨_, fun F _ => b3 b F⟩
        | add x y _ _ hx hy =>
          obtain ⟨μ, hμ⟩ := hx
          obtain ⟨ν, hν⟩ := hy
          exact ⟨μ + ν, fun F hF => by rw [map_add, LinearMap.add_apply, hμ F hF, hν F hF, add_smul]⟩
        | mul x y _ _ hx hy =>
          obtain ⟨μ, hμ⟩ := hx
          obtain ⟨ν, hν⟩ := hy
          exact ⟨ν * μ, fun F hF => by rw [map_mul, Module.End.mul_apply, hν F hF, map_smul, hμ F hF, smul_smul]⟩)
    refine ⟨z, RingHom.ext fun b => ?_, fun t F hF => hz t F hF⟩
    refine smul_left_injective K (m := (⟨v, hv.2⟩ : E)) (fun h => hv0 (congrArg Subtype.val h)) ?_
    exact (hz _ ⟨v, hv.2⟩ hv.1).symm.trans (b3 b _)
end Abs
universe u in
private theorem pa_main {A K M W ι : Type} [CommRing A] [Field K] [AddCommGroup M] [Module A M]
    [AddCommGroup W] [Module K W] {J : Type u} (Y0 Y : Submodule A M) [Module.Free A Y0] [Module.Finite A Y] (hle : Y ≤ Y0)
    (op : ι → Module.End A M)
    [hc : Fact (CommOn Y op)] (e : Module.End A Y0) (he : e ∈ heckeAlg Y0 op)
    (hi : IsIdempotentElem e) (hY : ∀ y : Y0, (y : M) ∈ Y ↔ e y = y) (χ : A →+* K) (sp : M → W)
    (hadd : ∀ f ∈ Y0, ∀ f' ∈ Y0, sp (f + f') = sp f + sp f') (hsmul : ∀ f ∈ Y0, ∀ b : A, sp (b • f) = χ b • sp f)
    (hind : ∀ (κ : Type) (b : Module.Basis κ A Y0), LinearIndependent K fun i => sp (b i))
    (opC : ι → Module.End K W) (hop : ∀ i, ∀ f ∈ Y0, sp (op i f) = opC i (sp f))
    (O E : Submodule K W) (hO : Submodule.span K (sp '' Y0) = O) (hE : E = Submodule.span K (sp '' Y))
    (Z : J → Submodule K W) (hZ : ∀ j i, ∀ F ∈ Z j, opC i F ∈ Z j) (hOZ : O = ⨆ j, Z j ⊓ O) :
    E ≤ O ∧ E = ⨆ j, Z j ⊓ E ∧ ∃ act : heckeAlg Y op →+* Module.End K E,
      (∀ (t : heckeAlg Y op) (f : Y) (F : E), (F : W) = sp f → (act t F : W) = sp ((t : Module.End A Y) f : Y)) ∧
      (∀ i (F : E), (act (heckeGen Y op i) F : W) = opC i F) ∧
      (∀ (b : A) (F : E), act (algebraMap A _ b) F = χ b • F) ∧
      (∀ z : heckeAlg Y op →+* K, z.comp (algebraMap A _) = χ →
        ∃ j F, F ≠ 0 ∧ F ∈ Z j ⊓ E ∧ ∀ i, opC i F = z (heckeGen Y op i) • F) ∧
      (∀ Z' : Submodule K W, Z' ⊓ E ≠ ⊥ → (∀ i, ∃ μ : K, ∀ F ∈ Z' ⊓ E, opC i F = μ • F) →
        ∃ z : heckeAlg Y op →+* K, z.comp (algebraMap A _) = χ ∧
          ∀ t (F : E), (F : W) ∈ Z' → act t F = z t • F) := by
  letI : Algebra A K := χ.toAlgebra
  letI : Module A W := Module.compHom W χ
  haveI : IsScalarTower A K W := ⟨fun a k w => mul_smul (χ a) k w⟩
  let s : Y0 →ₗ[A] W :=
    { toFun := fun f => sp f
      map_add' := fun f g => hadd _ f.2 _ g.2
      map_smul' := fun b f => hsmul _ f.2 b }
  refine ⟨hE ▸ hO ▸ Submodule.span_mono (Set.image_mono hle),
    pa_inst Y0 Y hle op e he hi hY s ?_ opC (fun i f g h => ?_) O E ?_ ?_ Z hZ hOZ⟩
  · let b := Module.Free.chooseBasis A Y0
    have h1 : s.liftBaseChange K = Finsupp.linearCombination K (fun i => sp (b i)) ∘ₗ (b.baseChange K).repr.toLinearMap :=
      (b.baseChange K).ext fun i => by
        rw [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.linearCombination_single,
          Module.Basis.baseChange_apply, LinearMap.liftBaseChange_tmul]
        rfl
    rw [h1, LinearMap.coe_comp]
    exact Function.Injective.comp (hind _ b) (b.baseChange K).repr.injective
  · change sp g = opC i (sp f)
    rw [h, hop i _ f.2]
  · rw [← hO, Set.image_eq_range]; rfl
  · rw [hE, Set.image_eq_range]; rfl
private theorem pa_pt {O A T K K' : Type} [CommRing O] [CommRing A] [CommRing T] [Field K] [Field K'] [Algebra O A]
    [Algebra O T] [Algebra A T] [IsScalarTower O A T] [Algebra O K] (ι : K ≃+* K') (x : A →ₐ[O] K) (z : T →+* K')
    (hz : z.comp (algebraMap A T) = ι.toRingHom.comp x.toRingHom) :
    ∃ y : T →ₐ[O] K, y.toRingHom.comp (algebraMap A T) = x.toRingHom ∧ ∀ t, ι (y t) = z t := by
  have hz' : ∀ b, ι.symm (z (algebraMap A T b)) = x b := fun b => ι.symm_apply_eq.2 (RingHom.congr_fun hz b)
  refine ⟨{ ι.symm.toRingHom.comp z with commutes' := fun b => ?_ }, RingHom.ext hz', fun t => ι.apply_symm_apply _⟩
  exact (congrArg (fun t => ι.symm (z t)) (IsScalarTower.algebraMap_apply O A T b)).trans ((hz' _).trans (x.commutes b))
universe u in
private theorem pa_fin {R A K K' M W ι : Type} [CommRing R] [CommRing A] [Algebra R A] [Field K] [Field K'] [Algebra R K']
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
    [AddCommGroup W] [Module K W] {J : Type u} (Y0 Y : Submodule A M) [Module.Free A Y0] [Module.Finite A Y] (hle : Y ≤ Y0)
    (op : ι → Module.End A M)
    [hc : Fact (CommOn Y op)] (e : Module.End A Y0) (he : e ∈ heckeAlg Y0 op)
    (hi : IsIdempotentElem e) (hY : ∀ y : Y0, (y : M) ∈ Y ↔ e y = y) (φ : K' ≃+* K) (x : A →ₐ[R] K') (sp : M → W)
    (hadd : ∀ f ∈ Y0, ∀ f' ∈ Y0, sp (f + f') = sp f + sp f') (hsmul : ∀ f ∈ Y0, ∀ b : A, sp (b • f) = φ (x b) • sp f)
    (hind : ∀ (κ : Type) (b : Module.Basis κ A Y0), LinearIndependent K fun i => sp (b i))
    (opC : ι → Module.End K W) (hop : ∀ i, ∀ f ∈ Y0, sp (op i f) = opC i (sp f))
    (O E : Submodule K W) (hO : Submodule.span K (sp '' Y0) = O) (hE : E = Submodule.span K (sp '' Y))
    (Z : J → Submodule K W) (hZ : ∀ j i, ∀ F ∈ Z j, opC i F ∈ Z j) (hOZ : O = ⨆ j, Z j ⊓ O) :
    E ≤ O ∧ E = ⨆ j, Z j ⊓ E ∧ ∃ act : heckeAlg Y op →+* Module.End K E,
      (∀ (t : heckeAlg Y op) (f : Y) (F : E), (F : W) = sp f → (act t F : W) = sp ((t : Module.End A Y) f : Y)) ∧
      (∀ i (F : E), (act (heckeGen Y op i) F : W) = opC i F) ∧
      (∀ (b : A) (F : E), act (algebraMap A _ b) F = φ (x b) • F) ∧
      (∀ y : heckeAlg Y op →ₐ[R] K', y.toRingHom.comp (algebraMap A _) = x.toRingHom →
        ∃ j F, F ≠ 0 ∧ F ∈ Z j ⊓ O ∧ ∀ i, opC i F = φ (y (heckeGen Y op i)) • F) ∧
      (∀ Z' : Submodule K W, Z' ⊓ E ≠ ⊥ → (∀ i, ∃ μ : K, ∀ F ∈ Z' ⊓ O, opC i F = μ • F) →
        ∃ y : heckeAlg Y op →ₐ[R] K', y.toRingHom.comp (algebraMap A _) = x.toRingHom ∧
          ∀ t (F : E), (F : W) ∈ Z' → act t F = φ (y t) • F) := by
  obtain ⟨hEO, hsum, act, h1, h2, h3, h4, h5⟩ := pa_main Y0 Y hle op e he hi hY (φ.toRingHom.comp x.toRingHom) sp hadd
    hsmul hind opC hop O E hO hE Z hZ hOZ
  refine ⟨hEO, hsum, act, h1, h2, h3, fun y hy => ?_, fun Z' hne hsc => ?_⟩
  · obtain ⟨j, F, hF0, hF, h⟩ := h4 (φ.toRingHom.comp y.toRingHom) (by rw [RingHom.comp_assoc, hy])
    exact ⟨j, F, hF0, ⟨hF.1, hEO hF.2⟩, h⟩
  · obtain ⟨z, hz, h⟩ := h5 Z' hne fun i => (hsc i).imp fun μ hμ F hF => hμ F ⟨hF.1, hEO hF.2⟩
    obtain ⟨y, hy, hy'⟩ := pa_pt φ x z hz
    exact ⟨y, hy, fun t F hF => by rw [hy', h t F hF]⟩
private theorem pa_iso {H M : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup M] [Module ℂ M]
    {ρ : Representation ℂ H M} {Y : Submodule ℂ M} {σ : SmIrr H} (h : IsoSum ρ Y σ) (g : H) : ∀ F ∈ Y, ρ g F ∈ Y := by
  intro F hF
  refine (iSup_le (a := Y.comap (ρ g)) ?_) (h hF)
  rintro f _ ⟨v, rfl⟩
  change ρ g (f.1 v) ∈ Y
  rw [← f.2.1]
  exact f.2.2 ⟨_, rfl⟩
private theorem pa_pi {V M : Type} [Finite V] [DecidableEq V] {G : V → Type} [∀ v, Group (G v)] [AddCommGroup M] [Module ℂ M]
    (ρ : Representation ℂ (∀ v, G v) M) (Y : Submodule ℂ M) (h : ∀ v g, ∀ F ∈ Y, ρ (Pi.mulSingle v g) F ∈ Y)
    (g : ∀ v, G v) : ∀ F ∈ Y, ρ g F ∈ Y := by
  let S : Subgroup (∀ v, G v) :=
    { carrier := {g | (∀ F ∈ Y, ρ g F ∈ Y) ∧ ∀ F ∈ Y, ρ g⁻¹ F ∈ Y}
      mul_mem' := fun {a b} ha hb => ⟨fun F hF => by rw [map_mul]; exact ha.1 _ (hb.1 F hF),
        fun F hF => by rw [mul_inv_rev, map_mul]; exact hb.2 _ (ha.2 F hF)⟩
      one_mem' := ⟨fun F hF => by rw [map_one]; exact hF, fun F hF => by rw [inv_one, map_one]; exact hF⟩
      inv_mem' := fun {a} ha => ⟨ha.2, by rw [inv_inv]; exact ha.1⟩ }
  exact (Subgroup.pi_mem_of_mulSingle_mem (H := S) g fun v =>
    ⟨h v _, by rw [← Pi.mulSingle_inv]; exact h v _⟩).1
theorem hecke_operator_preserves_part {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ}
    [Fact l.Prime] {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) {d : ℕ}
    (ξ : GV n H.Sl →* GL (Fin d) ℂ) (Y : H.PartAltAlt ι lam ξ) (i : H.Op) : ∀ F ∈ Y.Y, H.opC ι lam d i F ∈ Y.Y := by
  classical
  have h1 : ∀ g : GV n H.Sl, ∀ F ∈ Y.Y, H.X.rpF ℂ d H.m g F ∈ Y.Y := by
    exact pa_pi _ _ fun v g => pa_iso (Y.isoL v) g
  intro F hF
  rcases i with x | x
  · change sphOp (H.atW ι d x.1.1) (x.2 + 1) F ∈ _
    rw [Y.sph x.1 _ F hF]
    exact Y.Y.smul_mem _ hF
  · refine Y.Y.smul_mem _ ?_
    exact finsum_induction (p := fun φ : Module.End ℂ (Fin H.m → H.X.Fn ℂ d) => φ F ∈ Y.Y) (zero_mem _)
      (fun _ _ => add_mem) fun q => h1 _ F hF
set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Hi.partAct0_alt :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop), H.AutomorphicHeckeSet ι P →
    ∀ (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ) (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d), H.IsSpec θ ι x.toRingHom lam ξ c0 sp →
    lam ∈ H.admitted → ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))], ∀ E : Submodule ℂ (Fin H.m → H.X.Fn ℂ d), E = Submodule.span ℂ (sp '' H.MK θ a K) → (E = ⨆ Y : {Y : H.PartAltAlt ι lam ξ // P lam Y.r}, Y.1.Y ⊓ E ∨ ¬ H.Good θ x.toRingHom lam) ∧ ∃ act : H.TK θ a K →+* Module.End ℂ E, (∀ (t : H.TK θ a K) (f : H.MK θ a K) (F : E), (F : Fin H.m → H.X.Fn ℂ d) = sp f → (act t F : Fin H.m → H.X.Fn ℂ d) = sp ((t : Module.End A (H.MK θ a K)) f : H.MK θ a K)) ∧ (∀ i (F : E), (act (H.gen θ a K i) F : Fin H.m → H.X.Fn ℂ d) = H.opC ι lam d i F) ∧ (∀ (b : A) (F : E), act (algebraMap A _ b) F = ι (x b) • F) ∧ (∀ y : H.TK θ a K →ₐ[c.O] Qbar l, y.toRingHom.comp (algebraMap A _) = x.toRingHom → ∃ (Y : H.PartAltAlt ι lam ξ) (F : Fin H.m → H.X.Fn ℂ d) (e : ℕ), P lam Y.r ∧ c0 ≤ e ∧ F ≠ 0 ∧ F ∈ Y.Y ⊓ H.OrdAt θ ι x.toRingHom lam ξ K e ∧ ∀ i, H.opC ι lam d i F = ι (y (H.gen θ a K i)) • F) ∧ (H.Good θ x.toRingHom lam → ∀ Y : H.PartAltAlt ι lam ξ, Y.Y ⊓ E ≠ ⊥ → ∃ y : H.TK θ a K →ₐ[c.O] Qbar l, y.toRingHom.comp (algebraMap A _) = x.toRingHom ∧ ∀ t (F : E), (F : Fin H.m → H.X.Fn ℂ d) ∈ Y.Y → act t F = ι (y t) • F) := by
  intro hN L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι P hP x lam d ξ c0 sp hsp hlam a K _ E hE
  haveI : Finite (ResidueField c.O) := by
    haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (UpperTheory.V.Base.dvrFacts l c.O).2.2.1
    haveI : Finite (ResidueField ℤ_[l]) := IsCNL.finite
    exact Module.finite_of_finite (ResidueField ℤ_[l])
  haveI : IsCNL A := IsCNL.ofCO c.O A
  obtain ⟨h0, hfin, hfree, hK⟩ := hiComm L Ω l n c H hH A θ hθ K
  haveI := (hK a).2.1
  obtain ⟨e, he, hi, hY, -⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locIdem A _ _ _ (H.op A) (fun i => algebraMap c.O A (a i)) h0
  obtain ⟨hEO, hsum, act, h1, h2, h3, h4, h5⟩ := pa_fin (H.X.Ord (H.τA A) θ (H.lev K)) (H.MK θ a K) inf_le_left (H.op A)
    e he hi hY ι x sp (hsp.add K) (hsp.smul K) (hsp.indep K) (H.opC ι lam d) (hsp.op K)
    _ E (hsp.span K c0 le_rfl) hE (fun Y : {Y : H.PartAltAlt ι lam ξ // P lam Y.r} => Y.1.Y)
    (fun Y => _root_.hecke_operator_preserves_part H ι lam ξ Y.1) (_root_.UpperTheory.V.Hi.clParts_alt L Ω l n c H hH A θ hθ ι P hP x lam d ξ c0 sp hsp hlam K c0 le_rfl).2
  refine ⟨Or.inl hsum, act, h1, h2, h3, fun y hy => ?_, fun hg Y hne => ?_⟩
  · obtain ⟨Y, F, hF0, hF, h⟩ := h4 y hy
    exact ⟨Y.1, F, c0, Y.2, le_rfl, hF0, hF, h⟩
  · obtain ⟨ω, -, -, -, hω⟩ := _root_.UpperTheory.V.Hi.goodScalB_alt hN L Ω l n c H hH A θ hθ ι x lam d ξ c0 sp hsp hg Y K c0 le_rfl
      (fun h => hne (le_bot_iff.1 ((inf_le_inf_left _ hEO).trans h.le)))
    refine h5 Y.Y hne ?_
    rintro (i | i)
    · exact ⟨_, fun F hF => Y.sph i.1 _ F hF.1⟩
    · exact ⟨_, (hω i.1 i.2).2⟩
end
end
