import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.MemLevelOfLocalDepth
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TOutRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.AwayCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.DcMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.IsoCopy
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.IsoTypic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.SpanKeep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.LocEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdA
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.LocSubD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WStmtxx

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al
section LocEigAux
open UpperTheory.V.Hi UpperTheory.V.AlgebraTools
private theorem antitone_mem : ∀ {n : ℕ} (M : AddSubmonoid (Fin n → ℤ)), (∀ j ≤ n, fund n j ∈ M) → (-1 : Fin n → ℤ) ∈ M →
    ∀ a : Fin n → ℤ, Antitone a → a ∈ M := by
  intro n M h1 h2 a ha
  cases n with
  | zero =>
    have : a = 0 := Subsingleton.elim _ _
    rw [this]
    exact zero_mem _
  | succ N =>
    have hone : (1 : Fin (N + 1) → ℤ) ∈ M := by
      have := h1 (N + 1) le_rfl
      convert this using 1
      funext i
      simp [fund, i.2]
    let A : ℕ → ℤ := fun m => a ⟨min m N, by omega⟩
    have hA : ∀ m, A (m + 1) ≤ A m := fun m => ha (by
      simp only [Fin.mk_le_mk]
      omega)
    have tel : ∀ (m i : ℕ), i ≤ m → ∑ j ∈ Finset.range m, (if i < j + 1 then A j - A (j + 1) else 0) = A i - A m := by
      intro m
      induction m with
      | zero =>
        intro i hi
        obtain rfl : i = 0 := by omega
        simp
      | succ m ih =>
        intro i hi
        rw [Finset.sum_range_succ]
        by_cases h : i ≤ m
        · rw [ih i h, if_pos (by omega)]
          ring
        · obtain rfl : i = m + 1 := by omega
          rw [if_neg (by omega), Finset.sum_eq_zero]
          · simp
          · intro j hj
            have := Finset.mem_range.1 hj
            rw [if_neg (by omega)]
    have key : a = (A N) • (1 : Fin (N + 1) → ℤ) + ∑ j ∈ Finset.range N, (A j - A (j + 1)).toNat • fund (N + 1) (j + 1) := by
      funext i
      have hi : A i = a i := by
        show a _ = a i
        congr 1
        ext
        have := i.2
        simp only
        omega
      have h3 : ∀ j ∈ Finset.range N, (A j - A (j + 1)).toNat • fund (N + 1) (j + 1) i =
          if (i : ℕ) < j + 1 then A j - A (j + 1) else 0 := by
        intro j _
        have : (((A j - A (j + 1)).toNat : ℕ) : ℤ) = A j - A (j + 1) := Int.toNat_of_nonneg (sub_nonneg.2 (hA j))
        simp only [fund, nsmul_eq_mul, this]
        split_ifs <;> simp
      have h4 := tel N i (by have := i.2; omega)
      simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, Finset.sum_apply]
      rw [Finset.sum_congr rfl h3, h4, hi]
      ring
    rw [key]
    refine add_mem ?_ (sum_mem fun j hj => nsmul_mem (h1 _ (by have := Finset.mem_range.1 hj; omega)) _)
    obtain ⟨m, e | e⟩ := (A N).eq_nat_or_neg
    · rw [e, natCast_zsmul]
      exact nsmul_mem hone m
    · rw [e, neg_smul, ← smul_neg, natCast_zsmul]
      exact nsmul_mem h2 m
private theorem u_operator_torus_eigen {G : Type} [Group G] (I : Iwa G) {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (π : Representation A G M) {t : G} (ht : t ∈ I.T) {v : M} (hv : v ∈ fixd π I.N) {c : A} (hc : π t v = c • v) :
    I.uOp π t v = c • v := by
  have h : (I.Nconj t).subgroupOf I.N = ⊤ := by
    rw [Subgroup.subgroupOf_eq_top]
    intro x hx
    refine ⟨t⁻¹ * x * t, by simpa using I.T_N t⁻¹ (inv_mem ht) x hx, ?_⟩
    show t * (t⁻¹ * x * t) * t⁻¹ = x
    group
  haveI : Subsingleton (I.N ⧸ (I.Nconj t).subgroupOf I.N) := by
    rw [h]
    exact QuotientGroup.subsingleton_quotient_top
  letI := Unique.mk' (I.N ⧸ (I.Nconj t).subgroupOf I.N)
  rw [Iwa.uOp, finsum_unique, map_mul, Module.End.mul_apply, hc, map_smul, hv _ (SetLike.coe_mem _)]
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
private noncomputable def mu (ψ : Fin n → kˣ →* ℂˣ) (i : Fin n) : kˣ →* ℂˣ :=
  ψ i * (absPow k ((modExp (fun _ : Fin n => Unit) i : ℂ) / 2))⁻¹
private theorem expo_eq (ψ : Fin n → kˣ →* ℂˣ) (d : Fin n → kˣ) : Dict.expo ψ d = ((torusChar (mu ψ) d : ℂˣ) : ℂ) := by
  have hd : ∀ i, Matrix.GeneralLinearGroup.det (leviTorus k (Fin n) d i) = d i :=
    congrFun ((leviTorus k (Fin n)).left_inv d)
  simp [Dict.expo, deltaHalf_apply, hd, mu, Finset.prod_mul_distrib]
private noncomputable def omg (ψ : Fin n → kˣ →* ℂˣ) (i : Fin n) : kˣ →* ℂˣ := ψ i * absPow k (-(((n : ℂ) - 1) / 2))
private theorem om_shift (ψ : Fin n → kˣ →* ℂˣ) : (fun i => omg ψ i * absPow k (((n : ℂ) - 1) / 2)) = ψ := by
  funext i
  rw [omg, mul_assoc, ← absPow_add, neg_add_cancel, absPow_zero, mul_one]
private theorem om_unit (ψ : Fin n → kˣ →* ℂˣ) (i : Fin n) {y : kˣ} (hy : valuation k (y : k) = 1) : omg ψ i y = ψ i y := by
  simp [omg, isUnram_absPow k _ y hy]
private theorem mu_unit (ψ : Fin n → kˣ →* ℂˣ) (i : Fin n) {y : kˣ} (hy : valuation k (y : k) = 1) : mu ψ i y = ψ i y := by
  simp [mu, isUnram_absPow k _ y hy]
private theorem mu_unif (ψ : Fin n → kˣ →* ℂˣ) (i : Fin n) :
    (mu ψ i (UpperTheory.V.Hi.unif k) : ℂ) = (omg ψ i (UpperTheory.V.Hi.unif k) : ℂ) * ((Nat.card 𝓀[k] : ℂ) ^ (i : ℕ))⁻¹ := by
  have hq : nabs k (UpperTheory.V.Hi.unif k) = (Nat.card 𝓀[k] : ℝ)⁻¹ := GlobalTheory.GLDoubling.nabs_unif GlAx.unif_spec
  have e : mu ψ i = omg ψ i * absPow k ((i : ℕ) : ℂ) := by
    have hi := i.2
    rw [mu, omg, mul_assoc, ← absPow_add, ← absPow_neg, modExp_fin _ (fun _ => by simp)]
    congr 2
    push_cast
    ring
  rw [e, MonoidHom.mul_apply, Units.val_mul, val_absPow, hq, Complex.cpow_natCast]
  simp
private theorem mu_fund (ψ : Fin n → kˣ →* ℂˣ) (j : ℕ) :
    ((torusChar (mu ψ) (fun i => UpperTheory.V.Hi.unif k ^ fund n j i) : ℂˣ) : ℂ) = psEig (omg ψ) j := by
  rw [torusChar_apply, Units.coe_prod, psEig, Finset.prod_filter]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : (i : ℕ) < j
  · simp only [fund, if_pos h, zpow_one]
    exact mu_unif ψ i
  · simp [fund, if_neg h]
private theorem diagT_inj : Function.Injective (diagT k (Fin n)) := by
  intro s t h
  funext i
  have := congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i i) h
  simp only [val_diagT, Matrix.diagonal_apply_eq] at this
  exact Units.ext this
private noncomputable def phi (ω : Fin n → kˣ →* ℂˣ) : (glIwa k n).T →* ℂˣ :=
  ((torusChar ω)⁻¹ : (Fin n → kˣ) →* ℂˣ).comp ((torusO k (Fin n)).subtype.comp
    ((torusO k (Fin n)).equivMapOfInjective (diagT k (Fin n)) diagT_inj).symm.toMonoidHom)
private theorem phi_diag (ω : Fin n → kˣ →* ℂˣ) (u : Fin n → kˣ) (hu : u ∈ torusO k (Fin n)) :
    phi ω ⟨diagT k (Fin n) u, u, hu, rfl⟩ = (torusChar ω u)⁻¹ := by
  have : ((torusO k (Fin n)).equivMapOfInjective (diagT k (Fin n)) diagT_inj).symm ⟨diagT k (Fin n) u, u, hu, rfl⟩ = ⟨u, hu⟩ := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  exact congrArg (fun x : torusO k (Fin n) => (torusChar ω (x : Fin n → kˣ))⁻¹) this
private theorem phi_inv (ω : Fin n → kˣ →* ℂˣ) : IsInvOn (phi ω) ω := by
  intro i y
  have hu : (Pi.mulSingle i (y : kˣ) : Fin n → kˣ) ∈ torusO k (Fin n) := fun j => by
    by_cases h : j = i
    · subst h
      rw [Pi.mulSingle_eq_same]
      exact y.2
    · simp [Pi.mulSingle_eq_of_ne h]
  refine (phi_diag ω _ hu).trans ?_
  rw [torusChar_apply, Fintype.prod_eq_single i (fun j hj => by simp [Pi.mulSingle_eq_of_ne hj])]
  simp
private theorem upow_add (a b : Fin n → ℤ) : upow k n (a + b) = upow k n a * upow k n b := by
  rw [upow, upow, upow, ← map_mul]
  congr 1
  funext i
  simp [_root_.zpow_add]
private theorem upow_mem {a : Fin n → ℤ} (ha : Antitone a) : upow k n a ∈ (glIwa k n).P := ⟨a, ha, rfl⟩
private theorem uOp_upow {T : Type} [AddCommGroup T] [Module ℂ T] (τ : Representation ℂ (GL (Fin n) k) T)
    (ψ : Fin n → kˣ →* ℂˣ) {v : T} (hv : v ∈ fixd τ (glIwa k n).N)
    (hev : ∀ j ≤ n, (glIwa k n).uOp τ (al k n j) v = psEig (omg ψ) j • v) (a : Fin n → ℤ) (ha : Antitone a) :
    (glIwa k n).uOp τ (upow k n a) v = ((torusChar (mu ψ) (fun i => UpperTheory.V.Hi.unif k ^ a i) : ℂˣ) : ℂ) • v := by
  have E_add : ∀ a b : Fin n → ℤ, torusChar (mu ψ) (fun i => UpperTheory.V.Hi.unif k ^ (a + b) i) =
      torusChar (mu ψ) (fun i => UpperTheory.V.Hi.unif k ^ a i) * torusChar (mu ψ) (fun i => UpperTheory.V.Hi.unif k ^ b i) := by
    intro a b
    rw [← map_mul]
    congr 1
    funext i
    simp [_root_.zpow_add]
  have E_zero : torusChar (mu ψ) (fun i => UpperTheory.V.Hi.unif k ^ (0 : Fin n → ℤ) i) = 1 := by
    have : (fun i => UpperTheory.V.Hi.unif k ^ (0 : Fin n → ℤ) i) = 1 := by
      funext i
      simp
    rw [this, map_one]
  have mulOp := fun x y hx hy => (uOpMul _ (glIwa k n) ℂ T τ x y hx hy v hv)
  let M : AddSubmonoid (Fin n → ℤ) :=
    { carrier := {a | Antitone a ∧ (glIwa k n).uOp τ (upow k n a) v =
        ((torusChar (mu ψ) (fun i => UpperTheory.V.Hi.unif k ^ a i) : ℂˣ) : ℂ) • v}
      add_mem' := by
        rintro a b ⟨ha, ea⟩ ⟨hb, eb⟩
        refine ⟨ha.add hb, ?_⟩
        rw [upow_add, ← (mulOp _ _ (upow_mem ha) (upow_mem hb)).2.1, eb, map_smul, ea, smul_smul, E_add, Units.val_mul,
          mul_comm]
      zero_mem' := by
        refine ⟨fun _ _ _ => le_rfl, ?_⟩
        have h1 : upow k n (0 : Fin n → ℤ) = 1 := by
          rw [upow, ← (diagT k (Fin n)).map_one]
          congr 1
          funext i
          simp
        rw [h1, E_zero, (mulOp 1 1 (one_mem _) (one_mem _)).2.2.1]
        simp }
  have hfund : ∀ j ≤ n, fund n j ∈ M := by
    intro j hj
    refine ⟨fun i i' h => ?_, ?_⟩
    · have : (i : ℕ) ≤ i' := h
      change (if (i' : ℕ) < j then (1 : ℤ) else 0) ≤ if (i : ℕ) < j then 1 else 0
      split_ifs <;> omega
    · rw [mu_fund]
      exact hev j hj
  have hneg : (-1 : Fin n → ℤ) ∈ M := by
    have anti : Antitone (1 : Fin n → ℤ) := fun _ _ _ => le_rfl
    have anti' : Antitone (-1 : Fin n → ℤ) := fun _ _ _ => le_rfl
    have hinv : (upow k n (1 : Fin n → ℤ))⁻¹ = upow k n (-1) := by
      rw [inv_eq_iff_mul_eq_one, ← upow_add]
      rw [upow, ← (diagT k (Fin n)).map_one]
      congr 1
      funext i
      simp
    have h1 : fund n n = (1 : Fin n → ℤ) := by
      funext i
      simp [fund]
    obtain ⟨-, e1⟩ := hfund n le_rfl
    rw [h1] at e1
    have u1 := (mulOp _ _ (upow_mem anti) (upow_mem anti)).2.2.2.2 (by rw [hinv]; exact upow_mem anti')
    have u2 := (mulOp _ _ (upow_mem anti') (upow_mem anti')).2.2.2.2 (by rw [← hinv, inv_inv]; exact upow_mem anti)
    refine ⟨anti', ?_⟩
    rw [u2]
    have hE : torusChar (mu ψ) (fun i => UpperTheory.V.Hi.unif k ^ (-1 : Fin n → ℤ) i) =
        (torusChar (mu ψ) (fun i => UpperTheory.V.Hi.unif k ^ (1 : Fin n → ℤ) i))⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← E_add]
      rw [neg_add_cancel]
      exact E_zero
    rw [hE, ← hinv]
    rw [u1] at e1
    have h3 : τ (upow k n 1)⁻¹ (τ (upow k n 1) v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [e1, map_smul] at h3
    rw [Units.val_inv_eq_inv_val, eq_inv_smul_iff₀ (Units.ne_zero _)]
    exact h3
  exact (antitone_mem M hfund hneg a ha).2
end LocEigAux
theorem UpperTheory.V.Z.Sym.Al.exists_fixd_dc_eq_expo_smul_of_equiv_prinSeries :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (W : Sig.Lev k) (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → (∀ i, ∀ u ∈ W.H, ψ i u = 1) →
        ∀ (T : Type) [AddCommGroup T] [Module ℂ T] (τ : Representation ℂ (GL (Fin n) k) T), Nonempty (τ.Equiv (prinSeries ψ)) →
        ∃ v : T, v ≠ 0 ∧ v ∈ Hi.fixd τ (W.J n) ∧ ∀ d, Sig.SDom d → Hi.dc τ (W.J n) (W.J n) (Sig.dg d) v = expo ψ d • v := by
  intro hLit k _ _ _ _ n W ψ _ hH T _ _ τ he
  have hE : Nonempty (τ.Equiv (Hi.PS (omg ψ))) := by
    show Nonempty (τ.Equiv (prinSeries fun i => omg ψ i * absPow k (((n : ℂ) - 1) / 2)))
    rw [om_shift]
    exact he
  have hHv : ∀ y ∈ W.H, valuation k (y : k) = 1 := fun y hy => W.H_le hy
  obtain ⟨v, hv, hv0, hev⟩ := _root_.UpperTheory.V.Hi.exists_ne_zero_mem_eig_uOp_eq_psEig_smul_of_equiv_ps hLit k n T τ (omg ψ) hE W.c
    (fun i y hy => by rw [om_unit ψ i (hHv y (W.le hy)), hH i y (W.le hy)]) (phi (omg ψ)) (phi_inv _)
  have hT : ∀ (u : Fin n → kˣ) (hu : u ∈ torusO k (Fin n)), τ (diagT k (Fin n) u) v = ((torusChar (mu ψ) u : ℂˣ) : ℂ) • v := by
    intro u hu
    have h1 := hv.2.2 ⟨diagT k (Fin n) u, u, hu, rfl⟩
    rw [phi_diag _ u hu, inv_inv] at h1
    have h2 : torusChar (omg ψ) u = torusChar (mu ψ) u := by
      rw [torusChar_apply, torusChar_apply]
      exact Finset.prod_congr rfl fun i _ => by rw [om_unit ψ i (hu i), mu_unit ψ i (hu i)]
    rw [← h2]
    exact h1
  have hvJ : v ∈ Hi.fixd τ (W.J n) := by
    let S : Subgroup (GL (Fin n) k) :=
      { carrier := {g | τ g v = v}
        mul_mem' := fun {a b} ha hb => by
          show τ (a * b) v = v
          rw [map_mul, Module.End.mul_apply, hb, ha]
        one_mem' := by
          show τ 1 v = v
          simp
        inv_mem' := fun {a} ha => by
          show τ a⁻¹ v = v
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
    have hle : W.J n ≤ S := by
      refine sup_le (sup_le (fun g hg => hv.1 g hg) ?_) fun g hg => hv.2.1 g hg
      rintro _ ⟨s, hs, rfl⟩
      have hs' : ∀ i, s i ∈ W.H := fun i => hs i trivial
      show τ (diagT k (Fin n) s) v = v
      rw [hT s fun i => hHv _ (hs' i), torusChar_apply]
      have : ∏ i, mu ψ i (s i) = 1 := Finset.prod_eq_one fun i _ => by
        rw [mu_unit ψ i (hHv _ (hs' i)), hH i _ (hs' i)]
      rw [this, Units.val_one, one_smul]
    exact fun g hg => hle hg
  refine ⟨v, hv0, hvJ, fun d hd => ?_⟩
  have hDd : UpperTheory.V.AlgebraTools.Dom d := fun i j hij => by
    rcases hij.eq_or_lt with rfl | h
    · exact le_rfl
    · exact (hd i j h).le
  let a : Fin n → ℤ := fun i => GlobalTheory.SmGL.ord k (d i)
  have ha : Antitone a := fun i j hij => by
    have := hDd i j hij
    rw [Sig.val_ord, Sig.val_ord] at this
    exact (zpow_le_zpow_iff_right_of_lt_one₀ Hi.GlAx.unif_pos uniformizer_lt_one).1 this
  let p : Fin n → kˣ := fun i => Hi.unif k ^ a i
  let u : Fin n → kˣ := d / p
  have hu : u ∈ torusO k (Fin n) := fun i => Hi.GlAx.val_div_ord (d i)
  have hdu : d = u * p := by simp [u]
  have hDu : UpperTheory.V.AlgebraTools.Dom u := fun i j _ => by rw [hu i, hu j]
  have hDp : UpperTheory.V.AlgebraTools.Dom p := fun i j hij => by
    have e : ∀ i, valuation k (p i : k) = valuation k (d i : k) := fun i => by
      rw [hdu, Pi.mul_apply, Units.val_mul, map_mul, hu i, one_mul]
    rw [e, e]
    exact hDd i j hij
  have hI := ((Sig.finFacts k W).2.2.2.2.2 n).1 (Sig.dg d)
  have h0 := (UpperTheory.V.AlgebraTools.hkApply ℂ _ T τ (W.J n) (W.J n) (Sig.dg d) hI).1 ⟨v, hvJ⟩
  have hm := (Sig.hkMul k W n T τ).1 u p hDu hDp
  let X : Hi.fixd τ (W.J n) := ⟨v, hvJ⟩
  have h1 := (Sig.hkMul k W n T τ).2 p hDp X
  have h2 := (Sig.hkMul k W n T τ).2 u hDu X
  have hp : (Hi.glIwa k n).uOp τ (Sig.dg p) v = ((torusChar (mu ψ) p : ℂˣ) : ℂ) • v := uOp_upow τ ψ hv.1 hev a ha
  have hu' : (Hi.glIwa k n).uOp τ (Sig.dg u) v = ((torusChar (mu ψ) u : ℂˣ) : ℂ) • v :=
    u_operator_torus_eigen (Hi.glIwa k n) τ (t := diagT k (Fin n) u) ⟨u, hu, rfl⟩ hv.1 (hT u hu)
  have e1 : UpperTheory.V.AlgebraTools.hk τ (W.J n) (Sig.dg p) X = ((torusChar (mu ψ) p : ℂˣ) : ℂ) • X := Subtype.ext (h1.trans hp)
  have h0' : Hi.dc τ (W.J n) (W.J n) (Sig.dg d) v = (UpperTheory.V.AlgebraTools.hk τ (W.J n) (Sig.dg (u * p)) X : T) := by
    rw [← hdu]
    exact h0.symm
  have hc : torusChar (mu ψ) d = torusChar (mu ψ) u * torusChar (mu ψ) p := by
    rw [← map_mul, ← hdu]
  rw [h0', ← hm, Module.End.mul_apply, e1, map_smul]
  show ((torusChar (mu ψ) p : ℂˣ) : ℂ) • (UpperTheory.V.AlgebraTools.hk τ (W.J n) (Sig.dg u) X : T) = _
  rw [h2]
  show ((torusChar (mu ψ) p : ℂˣ) : ℂ) • (Hi.glIwa k n).uOp τ (Sig.dg u) v = _
  rw [hu', smul_smul, expo_eq, hc, Units.val_mul, mul_comm]
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al
theorem UpperTheory.V.Z.Sym.Al.exists_eigenvector_in_span_of_comp_eq_trivial :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (π : Submodule ℂ (UA L n → ℂ)), IsAutRepU π →
        ∀ w : Plc L, IsSplitAt w → ∀ (W : Sig.Lev (Kw w)) ψ, CompEq π w ψ → (∀ i, ∀ u ∈ W.H, ψ i u = 1) →
        ∀ φ : UA L n → V, φ ≠ 0 → CoefIn φ π →
        ∃ φ', φ' ≠ 0 ∧ InSpan w φ φ' ∧ (∀ x ∈ locU n w, cLoc w x ∈ W.J n → ∀ g, φ' (g * x) = φ' g) ∧ EigT φ' w W ψ := by
  intro hLit L _ _ _ n V _ _ _ π hπ w hw W ψ ⟨hsm, τ, hτ, ⟨e⟩⟩ hψ φ hφ hc
  obtain ⟨s1, -, s3, -⟩ := secSpec L n w hw
  let N : Submodule ℂ (UA L n → V) := Submodule.span ℂ {ψ' | ∃ x ∈ locU n w, ψ' = fun g => φ (g * x)}
  let ρ : Representation ℂ (GL (Fin n) (Kw w)) (UA L n → V) := (rightReg ℂ (UA L n) V).comp (secW n w)
  have hρ : ∀ h (a : UA L n → V) g, ρ h a g = a (g * secW n w h) := fun _ _ _ => rfl
  have hst : ∀ h, ∀ a ∈ N, ρ h a ∈ N := by
    intro h a ha
    refine Submodule.span_induction (p := fun a _ => ρ h a ∈ N) ?_ (by simp) (fun _ _ _ _ h1 h2 => by
      rw [map_add]; exact N.add_mem h1 h2) (fun c _ _ h1 => by rw [map_smul]; exact N.smul_mem c h1) ha
    rintro _ ⟨x, hx, rfl⟩
    refine Submodule.subset_span ⟨secW n w h * x, (locU n w).mul_mem (s1 h) hx, ?_⟩
    funext g
    rw [hρ, mul_assoc]
  let ν : Representation ℂ (GL (Fin n) (Kw w)) N :=
    { toFun := fun h => (ρ h).restrict (hst h)
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp }
  have hν : ∀ h (a : N), ((ν h a : N) : UA L n → V) = ρ h a := fun _ _ => rfl
  have hφN : φ ∈ N := Submodule.subset_span ⟨1, (locU n w).one_mem, by funext g; rw [mul_one]⟩
  have hco : ∀ a : N, CoefIn (a : UA L n → V) π := fun a =>
    (spanKeep L n V w φ a a.2).1 π hπ hc
  let b := Module.finBasis ℂ V
  let q : Fin (Module.finrank ℂ V) → N →ₗ[ℂ] π := fun i =>
    { toFun := fun a => ⟨b.coord i ∘ (a : UA L n → V), hco a _⟩
      map_add' := fun x y => Subtype.ext (by funext g; simp)
      map_smul' := fun c x => Subtype.ext (by funext g; simp) }
  haveI : Nontrivial N := ⟨⟨⟨φ, hφN⟩, 0, fun h => hφ (congrArg Subtype.val h)⟩⟩
  obtain ⟨f, hf0, hf⟩ := (isoCopy _ _ _ τ.ρ ((repOn hπ).comp (secW n w)) τ.irred
    (isoTypic L n π hπ w hw τ hτ)).2 N (Fin (Module.finrank ℂ V)) ν q
      (fun i h x => Subtype.ext rfl)
      (fun x hx => Subtype.ext (by
        funext g
        refine b.ext_elem fun i => ?_
        have : b.repr ((x : UA L n → V) g) i = 0 := congrFun (congrArg Subtype.val (hx i)) g
        simpa using this)) inferInstance
  have hinj : Function.Injective f := by
    haveI := τ.irred
    let Φ : τ.ρ.IntertwiningMap ν :=
      { toFun := f
        map_add' := f.map_add
        map_smul' := f.map_smul
        isIntertwining' := fun g => LinearMap.ext fun x => hf g x }
    refine (Representation.IsIrreducible.injective_or_eq_zero Φ).resolve_right fun h => hf0 ?_
    exact LinearMap.ext fun x => congrArg (fun Ψ : τ.ρ.IntertwiningMap ν => Ψ x) h
  obtain ⟨v, hv0, hvJ, hvE⟩ := _root_.UpperTheory.V.Z.Sym.Al.exists_fixd_dc_eq_expo_smul_of_equiv_prinSeries hLit (Kw w) n W ψ hsm hψ τ.V τ.ρ ⟨e⟩
  refine ⟨f v, fun h => hv0 (hinj (Subtype.ext (by simpa using h))), (f v).2, ?_, ?_⟩
  · intro x hx hJ g
    have h1 := hf (cLoc w x) v
    rw [hvJ _ hJ] at h1
    have h2 := congrFun (congrArg Subtype.val h1) g
    rw [hν, hρ, s3 x hx] at h2
    exact h2.symm
  · intro d hd
    have h1 := dcMap W τ.ρ ρ (N.subtype ∘ₗ f) (fun h x => by simp [hf, hν]) (Sig.dg d) v
    rw [hvE d hd] at h1
    simpa [EigAt, ρ] using h1.symm
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al
private theorem thinOut {α β : Type} [DecidableEq α] (f : α → β) (S T : Finset α) (hinj : Set.InjOn f (S : Set α)) :
    ∃ T' : Finset α, S ⊆ T' ∧ Set.InjOn f (T' : Set α) ∧ (∀ t ∈ T', t ∉ S → ∀ s ∈ S, f s ≠ f t) ∧
      ∀ t ∈ T, ∃ t' ∈ T', f t' = f t := by
  induction T using Finset.induction_on with
  | empty => exact ⟨S, subset_rfl, hinj, fun t h h' => absurd h h', by simp⟩
  | insert a T₀ _ ih =>
    obtain ⟨T', h1, h2, h3, h4⟩ := ih
    by_cases h : ∃ t' ∈ T', f t' = f a
    · refine ⟨T', h1, h2, h3, fun t ht => ?_⟩
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact h
      · exact h4 t ht
    · push_neg at h
      refine ⟨insert a T', h1.trans (Finset.subset_insert _ _), ?_, ?_, ?_⟩
      · intro x hx y hy hxy
        rcases Finset.mem_insert.1 (Finset.mem_coe.1 hx) with h₁ | h₁ <;>
          rcases Finset.mem_insert.1 (Finset.mem_coe.1 hy) with h₂ | h₂
        · rw [h₁, h₂]
        · subst h₁
          exact absurd hxy.symm (h y h₂)
        · subst h₂
          exact absurd hxy (h x h₁)
        · exact h2 h₁ h₂ hxy
      · intro t ht htS s hs
        rcases Finset.mem_insert.1 ht with rfl | ht
        · exact h s (h1 hs)
        · exact h3 t ht htS s hs
      · intro t ht
        rcases Finset.mem_insert.1 ht with rfl | ht
        · exact ⟨_, Finset.mem_insert_self _ _, rfl⟩
        · obtain ⟨t', a', b⟩ := h4 t ht
          exact ⟨t', Finset.mem_insert_of_mem a', b⟩
section
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
private theorem away_congr {n : ℕ} {w w' : Plc L} (h : w.under (𝓞 (Lp L)) = w'.under (𝓞 (Lp L))) :
    away n w = away n w' := by
  simp only [away, h]
private theorem cLoc_away {n : ℕ} {w : Plc L} {y : UA L n} (hy : y ∈ away n w) : cLoc w y = 1 :=
  Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hy w) rfl
private noncomputable def AT (S : Finset (Plc L)) (W : ∀ w : Plc L, Sig.Lev (Kw w)) (T : Finset (Plc L)) : Subgroup (UA L 2) :=
  lev (Kall L 2) S W ⊓ ⨅ w ∈ T, away 2 w
private theorem step [DecidableEq (Plc L)] {V : Type} [AddCommGroup V] [Module ℂ V] (S T₀ : Finset (Plc L))
    (W : ∀ w : Plc L, Sig.Lev (Kw w)) (w : Plc L)
    (hS : ∀ v ∈ S, v ≠ w → v.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)))
    (hT : ∀ t ∈ T₀, t.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)))
    (R : Representation ℂ (InfinitePlace L → GL (Fin 2) ℂ) V) (φ φ' : UA L 2 → V)
    (hspan : InSpan w φ φ') (hAF : IsAF R (AT S W (insert w T₀)) φ)
    (hinv : ∀ x ∈ locU 2 w, x ∈ Kall L 2 → (w ∈ S → cLoc w x ∈ (W w).J 2) → ∀ g, φ' (g * x) = φ' g) :
    IsAF R (AT S W T₀) φ' := by
  have h1 : AT S W (insert w T₀) ≤ away 2 w :=
    inf_le_right.trans (iInf₂_le w (Finset.mem_insert_self _ _))
  have h2 := (spanKeep L 2 V w φ φ' hspan).2.1 R _ h1 hAF
  refine ⟨h2.left, h2.inf, ?_⟩
  intro u hu g
  obtain ⟨x, hx, y, hy, rfl⟩ := (factor L 2 w).2.1 u
  obtain ⟨hlev, hTa⟩ := Subgroup.mem_inf.1 hu
  obtain ⟨hK, hJ⟩ := Subgroup.mem_inf.1 hlev
  have hxy := ((factor L 2 w).2.2.2.2.2 x hx y hy).1 hK
  have hJ' : ∀ v ∈ S, cLoc v (x * y) ∈ (W v).J 2 := fun v hv =>
    Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hJ v) hv
  have hyw : cLoc w y = 1 := cLoc_away hy
  have hyA : y ∈ AT S W (insert w T₀) := by
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hxy.2, ?_⟩, ?_⟩
    · refine Subgroup.mem_iInf.2 fun v => Subgroup.mem_iInf.2 fun hv => ?_
      show cLoc v y ∈ (W v).J 2
      by_cases hvw : v = w
      · subst hvw
        rw [hyw]
        exact one_mem _
      · have hxv : cLoc v x = 1 :=
          cLoc_away ((factor L 2 v).2.2.1 w (hS v hv hvw).symm hx)
        have := hJ' v hv
        rwa [map_mul, hxv, one_mul] at this
    · refine Subgroup.mem_iInf.2 fun t => Subgroup.mem_iInf.2 fun ht => ?_
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact hy
      · have hxt : x ∈ away 2 t := (factor L 2 t).2.2.1 w (hT t ht).symm hx
        have hxyt : x * y ∈ away 2 t := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hTa t) ht
        exact (Subgroup.mul_mem_cancel_left _ hxt).1 hxyt
  rw [← mul_assoc, h2.level y hyA, hinv x hx hxy.1 ?_]
  intro hwS
  have := hJ' w hwS
  rwa [map_mul, hyw, mul_one] at this
end
theorem UpperTheory.V.Z.Sym.Al.inVec_alt :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (π : Submodule ℂ (UA L 2 → ℂ)), IsAutRepU π → ∀ j : ℕ,
        (∀ v : InfinitePlace L, ∃ lam, HasWeightAt π v.embedding lam ∧ lam.w 0 - lam.w 1 = j) →
        ∀ S : Finset (Plc L), Places (S : Set (Plc L)) →
        (∀ w : Plc L, (∀ w' ∈ S, w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))) → IsUnramU π w) →
        ∀ (W : ∀ w : Plc L, Sig.Lev (Kw w)) (ψ : ∀ w : Plc L, Fin 2 → (Kw w)ˣ →* ℂˣ),
        (∀ w ∈ S, CompEq π w (ψ w) ∧ ∀ i, ∀ u ∈ (W w).H, ψ w i u = 1) →
        ∃ (e : InfinitePlace L → ℤ) (φ : UA L 2 → Wt.VD (InfinitePlace L) j), φ ≠ 0 ∧ IsAF (repE j e) (lev (Kall L 2) S W) φ ∧
          ∀ w ∈ S, EigT φ w (W w) (ψ w) := by
  intro hN L _ _ _ π hπ j hwt S hS hun W ψ hψ
  classical
  haveI : FiniteDimensional ℂ (Wt.VD (InfinitePlace L) j) := Wt.finMH (InfinitePlace L) 2 _
  obtain ⟨e, φ₀, hne, hco, hAF⟩ := infVec L π hπ j hwt
  obtain ⟨U, hUo, hUi⟩ := openLev L 2 _ π hπ φ₀ hco
  obtain ⟨T, hT⟩ := (cof L 2).1 U hUo
  obtain ⟨T', hST, hthin, hsep, hcov⟩ := thinOut (fun w : Plc L => w.under (𝓞 (Lp L))) S T hS.inj
  have key : ∀ D : Finset (Plc L), D ⊆ T' →
      ∃ φ : UA L 2 → Wt.VD (InfinitePlace L) j, φ ≠ 0 ∧ CoefIn φ π ∧ IsAF (repE j e) (AT S W (T' \ D)) φ ∧
        ∀ w ∈ S, w ∉ T' \ D → EigT φ w (W w) (ψ w) := by
    intro D
    induction D using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨φ₀, hne, hco, ⟨hAF.left, hAF.inf, fun u hu g => hUi u ?_ g⟩, fun w hw hw' => ?_⟩
      · obtain ⟨hlev, hTa⟩ := Subgroup.mem_inf.1 hu
        refine hT (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hlev).1, ?_⟩)
        refine Subgroup.mem_iInf.2 fun t => Subgroup.mem_iInf.2 fun ht => ?_
        obtain ⟨t', ht', hf⟩ := hcov t ht
        rw [← away_congr hf]
        exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hTa t') (by simpa using ht')
      · exact absurd (by simpa using hST hw) hw'
    | insert w D₀ hwD ih =>
      intro hsub
      have hwT : w ∈ T' := hsub (Finset.mem_insert_self _ _)
      obtain ⟨φ, hφ, hc, hA, hE⟩ := ih ((Finset.subset_insert _ _).trans hsub)
      have hins : T' \ D₀ = insert w (T' \ insert w D₀) := by
        ext t
        by_cases h : t = w
        · subst h; simp [hwT, hwD]
        · simp [h]
      have hTs : ∀ t ∈ T' \ insert w D₀, t.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)) := by
        intro t ht hf
        have ht' := Finset.mem_sdiff.1 ht
        exact ht'.2 (by rw [hthin (Finset.mem_coe.2 ht'.1) (Finset.mem_coe.2 hwT) hf]; exact Finset.mem_insert_self _ _)
      rw [hins] at hA
      have hE' : ∀ v ∈ S, v ≠ w → v ∉ T' \ insert w D₀ → EigT φ v (W v) (ψ v) := by
        intro v hv hvw hvT
        refine hE v hv ?_
        rw [hins]
        simp [hvw, hvT]
      by_cases hwS : w ∈ S
      · have hSs : ∀ v ∈ S, v ≠ w → v.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)) :=
          fun v hv hvw hf => hvw (hS.inj (Finset.mem_coe.2 hv) (Finset.mem_coe.2 hwS) hf)
        obtain ⟨φ', hφ', hspan, hinv, hEig⟩ :=
          _root_.UpperTheory.V.Z.Sym.Al.exists_eigenvector_in_span_of_comp_eq_trivial hN L 2 _ π hπ w (hS.split w hwS) (W w) (ψ w) (hψ w hwS).1 (hψ w hwS).2 φ hφ hc
        have hk := spanKeep L 2 _ w φ φ' hspan
        refine ⟨φ', hφ', hk.1 π hπ hc, step S _ W w hSs hTs _ φ φ' hspan hA
          (fun x hx _ hJ g => hinv x hx (hJ hwS) g), fun v hv hvT => ?_⟩
        by_cases hvw : v = w
        · subst hvw; exact hEig
        · exact fun d hd => hk.2.2 v (hS.split v hv) (hSs v hv hvw) _ d _ (hE' v hv hvw hvT d hd)
      · have hSs : ∀ v ∈ S, v ≠ w → v.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)) :=
          fun v hv _ => hsep w hwT hwS v hv
        obtain ⟨φ', hφ', hspan, hinv⟩ :=
          spanSph L 2 _ π hπ w (hun w (hsep w hwT hwS)) φ hφ hc
        have hk := spanKeep L 2 _ w φ φ' hspan
        refine ⟨φ', hφ', hk.1 π hπ hc, step S _ W w hSs hTs _ φ φ' hspan hA
          (fun x hx hK _ g => hinv x ⟨hx, hK⟩ g), fun v hv hvT => ?_⟩
        have hvw : v ≠ w := fun h => hwS (h ▸ hv)
        exact fun d hd => hk.2.2 v (hS.split v hv) (hSs v hv hvw) _ d _ (hE' v hv hvw hvT d hd)
  obtain ⟨φ, hφ, -, hA, hE⟩ := key T' subset_rfl
  refine ⟨e, φ, hφ, ⟨hA.left, hA.inf, fun u hu g => hA.level u ?_ g⟩, fun w hw => hE w hw (by simp)⟩
  exact Subgroup.mem_inf.2 ⟨hu, by simp⟩
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain ValuativeRel Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
section General
variable {G V : Type} [CommGroup G] [AddCommGroup V] [Module ℂ V]
private theorem pow_comm_rep (ρ : Representation ℂ G V) (t g : G) (c : ℂ) (m : ℕ) (v : V) :
    ((ρ t - algebraMap ℂ (Module.End ℂ V) c) ^ m) (ρ g v) =
      ρ g (((ρ t - algebraMap ℂ (Module.End ℂ V) c) ^ m) v) := by
  have h : Commute (ρ t - algebraMap ℂ (Module.End ℂ V) c) (ρ g) :=
    Commute.sub_left ((Commute.all t g).map ρ) (Algebra.commutes c (ρ g))
  exact LinearMap.congr_fun (h.pow_left m).eq v
private theorem pow_mem_sub (ρ : Representation ℂ G V) (N : Subrepresentation ρ) (t : G) (c : ℂ) (m : ℕ)
    (v : V) (hv : v ∈ N.toSubmodule) : ((ρ t - algebraMap ℂ (Module.End ℂ V) c) ^ m) v ∈ N.toSubmodule := by
  induction m with
  | zero => simpa using hv
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, LinearMap.sub_apply, Module.algebraMap_end_apply]
    exact sub_mem (N.apply_mem_toSubmodule t ih) (N.toSubmodule.smul_mem c ih)
private theorem exists_nil {ρ : Representation ℂ G V} (hl : HasFiniteLength ρ) {c : G → ℂ} {x : V} (hx : x ≠ 0)
    (hxc : ∀ t, ∃ m : ℕ, ((ρ t - algebraMap ℂ (Module.End ℂ V) (c t)) ^ m) x = 0) :
    ∃ N : Subrepresentation ρ, N ≠ ⊤ ∧
      ∀ t, ∃ m : ℕ, ∀ v, ((ρ t - algebraMap ℂ (Module.End ℂ V) (c t)) ^ m) v ∈ N.toSubmodule := by
  haveI := ((hasFiniteLength_iff_wellFounded ρ).1 hl).1
  obtain ⟨N, hN, hmax⟩ := (wellFounded_gt (α := Subrepresentation ρ)).has_min {N | x ∉ N.toSubmodule}
    ⟨⊥, fun h => hx ((Submodule.mem_bot ℂ).1 h)⟩
  refine ⟨N, fun h => hN (by rw [h]; trivial), fun t => ?_⟩
  set f := ρ t - algebraMap ℂ (Module.End ℂ V) (c t) with hf
  let K : ℕ →o Subrepresentation ρ :=
    ⟨fun m => ⟨N.toSubmodule.comap (f ^ m), fun g v hv => by
        show (f ^ m) (ρ g v) ∈ N.toSubmodule
        rw [hf, pow_comm_rep]
        exact N.apply_mem_toSubmodule g hv⟩,
      monotone_nat_of_le_succ fun m v hv => by
        show (f ^ (m + 1)) v ∈ N.toSubmodule
        rw [add_comm, pow_add, Module.End.mul_apply]
        exact pow_mem_sub ρ N t _ 1 _ hv⟩
  obtain ⟨a, ha⟩ := WellFoundedGT.monotone_chain_condition K
  obtain ⟨b, hb⟩ := hxc t
  let R : Subrepresentation ρ := ⟨N.toSubmodule ⊔ LinearMap.range (f ^ (a + b)), fun g v hv => by
    obtain ⟨y, hy, _, ⟨z, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add]
    exact Submodule.add_mem_sup (N.apply_mem_toSubmodule g hy) ⟨ρ g z, by rw [hf, pow_comm_rep]⟩⟩
  have hR : x ∉ R.toSubmodule := fun hv => by
    obtain ⟨y, hy, _, ⟨z, rfl⟩, h⟩ := Submodule.mem_sup.1 hv
    have h1 : z ∈ (K (b + (a + b))).toSubmodule := by
      show (f ^ (b + (a + b))) z ∈ N.toSubmodule
      rw [pow_add, Module.End.mul_apply, eq_sub_of_add_eq' h, map_sub, hb, zero_sub]
      exact neg_mem (pow_mem_sub ρ N t _ b _ hy)
    rw [← ha _ (by omega), ha (a + b) (by omega)] at h1
    exact hN (h ▸ add_mem hy h1)
  have hNR : N ≤ R := fun v hv => Submodule.mem_sup_left (S := N.toSubmodule) hv
  have hE : N = R := by
    by_contra hne
    exact hmax R hR (lt_of_le_of_ne hNR hne)
  refine ⟨a + b, fun v => ?_⟩
  rw [hE]
  exact Submodule.mem_sup_right ⟨v, rfl⟩
variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace.SeparableSpace G]
private theorem exists_form {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (hl : HasFiniteLength ρ) {χ : G →* ℂˣ}
    {x : V} (hx : x ≠ 0)
    (hxc : ∀ t, ∃ m : ℕ, ((ρ t - algebraMap ℂ (Module.End ℂ V) (χ t : ℂ)) ^ m) x = 0) :
    IsSmoothChar χ ∧ ∃ l : V →ₗ[ℂ] ℂ, l ≠ 0 ∧ ∀ g v, l (ρ g v) = (χ g : ℂ) * l v := by
  obtain ⟨T, hT, hnil⟩ := exists_nil hl hx hxc
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
  have hμχ : μ = χ := MonoidHom.ext fun t => by
    obtain ⟨m, hm⟩ := hnil t
    have h1 : ∀ m : ℕ, l (((ρ t - algebraMap ℂ (Module.End ℂ V) (χ t : ℂ)) ^ m) v) =
        ((μ t : ℂ) - χ t) ^ m * l v := fun m => by
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ', Module.End.mul_apply, LinearMap.sub_apply, Module.algebraMap_end_apply, map_sub, hle,
          map_smul, ih, smul_eq_mul]
        ring
    have h2 := hlM (hTM (hm v))
    rw [LinearMap.mem_ker, h1] at h2
    exact Units.ext (sub_eq_zero.1 (pow_eq_zero_iff'.1 ((mul_eq_zero.1 h2).resolve_right hv)).1)
  subst hμχ
  refine ⟨?_, l, hl0, hle⟩
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset ((hρ v).mem_nhds (by simp)) ?_)
  intro g hg
  have hg' : ρ g v = v := hg
  have h := hle g v
  rw [hg'] at h
  exact Units.ext (mul_right_cancel₀ hv (h.symm.trans (one_mul _).symm))
end General
private theorem smul_cancel {M : Type} [AddCommGroup M] [Module ℂ M] {c : ℂ} (hc : c ≠ 0) {a b : M}
    (h : c • a = c • b) : a = b :=
  smul_right_injective M hc h
private theorem val_nontrivial {k : Type} [Field k] [ValuativeRel k] : Nontrivial (ValueGroupWithZero k) :=
  GroupWithZero.toNontrivial
attribute [local instance] val_nontrivial
section Lev
open GlobalTheory.IwahoriInj GlobalTheory.IwahoriTraceProof
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
private theorem sdom_of_step {k : Type} [Field k] [ValuativeRel k] {n : ℕ} (s : Fin n → kˣ) (c : kˣ)
    (h1 : valuation k (c : k) ≤ 1)
    (h2 : ∀ i j : Fin n, i < j → valuation k (s i : k) * valuation k (c : k) < valuation k (s j : k)) :
    Sig.SDom fun i : Fin n => s i * c ^ (n - (i : ℕ)) := by
  intro i j hij
  have hj := j.2
  have hij' : (i : ℕ) < j := hij
  have e : n - (i : ℕ) = 1 + ((n - j) + (j - i - 1)) := by omega
  have hc0 : 0 < valuation k (c : k) := zero_lt_iff.2 ((valuation k).ne_zero_iff.2 c.ne_zero)
  beta_reduce
  rw [e]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, pow_add, pow_one]
  rw [← mul_assoc]
  calc valuation k (s i : k) * valuation k (c : k) *
        (valuation k (c : k) ^ (n - (j : ℕ)) * valuation k (c : k) ^ ((j : ℕ) - i - 1))
      ≤ valuation k (s i : k) * valuation k (c : k) * valuation k (c : k) ^ (n - (j : ℕ)) := by
        rw [← mul_assoc]
        exact mul_le_of_le_one_right' (pow_le_one' h1 _)
    _ < valuation k (s j : k) * valuation k (c : k) ^ (n - (j : ℕ)) :=
        mul_lt_mul_of_pos_right (h2 i j hij) (pow_pos hc0 _)
private theorem exists_sdom {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} (t : Fin n → kˣ) :
    ∃ d : Fin n → kˣ, Sig.SDom d ∧ Sig.SDom (t * d) := by
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · exact ⟨1, fun i => h.elim i, fun i => h.elim i⟩
  obtain ⟨p, hp⟩ := Finite.exists_min
    (fun p : Fin n × Fin n => valuation k ((t p.2 * (t p.1)⁻¹ : kˣ) : k))
  obtain ⟨x, q, hq, hx⟩ := UpperTheory.V.AlgebraTools.exists_isUnif (k := k)
  have hx1 : valuation k (x : k) < 1 := by
    have h0 : valuation k (q : k) ≤ 1 := q.2
    have hne : valuation k (q : k) ≠ 1 := fun h =>
      hq.not_isUnit ((Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 h)
    rw [← hx]
    exact lt_of_le_of_ne h0 hne
  set c₀ : kˣ := t p.2 * (t p.1)⁻¹ with hc₀
  have hc1 : valuation k (c₀ : k) ≤ 1 := by simpa using hp (p.1, p.1)
  have hcx : valuation k ((c₀ * x : kˣ) : k) < 1 := by
    rw [Units.val_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hc1) hx1
  refine ⟨fun i => (c₀ * x) ^ (n - (i : ℕ)), ?_, ?_⟩
  · simpa using sdom_of_step (1 : Fin n → kˣ) (c₀ * x) hcx.le fun i j _ => by simpa using hcx
  · refine sdom_of_step t (c₀ * x) hcx.le fun i j _ => ?_
    have hle : valuation k (t i : k) * valuation k (c₀ : k) ≤ valuation k (t j : k) := by
      refine (mul_le_mul_right (hp (i, j)) (valuation k (t i : k))).trans (le_of_eq ?_)
      rw [← map_mul, ← Units.val_mul]
      congr 2
      simp
    have hj0 : 0 < valuation k (t j : k) := zero_lt_iff.2 ((valuation k).ne_zero_iff.2 (t j).ne_zero)
    rw [Units.val_mul, map_mul, ← mul_assoc]
    calc valuation k (t i : k) * valuation k (c₀ : k) * valuation k (x : k)
        ≤ valuation k (t j : k) * valuation k (x : k) := mul_le_mul_left hle _
      _ < valuation k (t j : k) * 1 := mul_lt_mul_of_pos_left hx1 hj0
      _ = valuation k (t j : k) := mul_one _
private theorem jqInj_dom {x : kˣ} (hx : valuation k (x : k) = uniformizer k) (m : ℕ) :
    Dom fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ))) := by
  intro i j hij
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀, hx]
  refine zpow_le_zpow_right_of_le_one₀ unif_pos uniformizer_lt_one.le ?_
  have : ((i : ℕ) : ℤ) ≤ (j : ℕ) := by exact_mod_cast Fin.le_def.1 hij
  nlinarith
private theorem jqInj_ev {x : kˣ} (hx : valuation k (x : k) = uniformizer k) {u : GL (Fin n) k}
    (hu : u ∈ unipB k (Fin n)) : ∀ᶠ m : ℕ in Filter.atTop,
      diagT k (Fin n) (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ)))) * u *
        (diagT k (Fin n) (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ)))))⁻¹ ∈ unipO k n := by
  have key : ∀ u ∈ unipB k (Fin n), ∀ᶠ m : ℕ in Filter.atTop, GlobalTheory.StepData.IntM
      (diagT k (Fin n) (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ)))) * u *
        (diagT k (Fin n) (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ)))))⁻¹).val := by
    intro u hu
    simp only [GlobalTheory.StepData.IntM, Filter.eventually_all]
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · filter_upwards [eventually_deep (u.val i j)] with m hm
      rw [← map_inv, diag_mul_mul_diag]
      have h1 : Deep (-((m : ℤ) * (i : ℕ)) + (m : ℤ) * (j : ℕ))
          ((x ^ (-((m : ℤ) * (i : ℕ))) * (x ^ (-((m : ℤ) * (j : ℕ))))⁻¹ : kˣ) : k) := by
        rw [← _root_.zpow_neg, neg_neg, ← _root_.zpow_add, Deep, Units.val_zpow_eq_zpow_val, map_zpow₀, hx]
      have h2 : ((i : ℕ) : ℤ) + 1 ≤ (j : ℕ) := by exact_mod_cast Fin.lt_def.1 h
      exact deep_zero_iff.1 ((h1.mul hm).mono (by nlinarith))
    · refine Filter.Eventually.of_forall fun m => ?_
      rw [((mem_unipB k).1 (conj_mem_unipB _ hu)).2 i]
      exact one_mem _
    · refine Filter.Eventually.of_forall fun m => ?_
      rw [((mem_unipB k).1 (conj_mem_unipB _ hu)).1 i j h]
      exact zero_mem _
  filter_upwards [key u hu, key _ (inv_mem hu)] with m h1 h2
  refine ⟨conj_mem_unipB _ hu, GlobalTheory.StepData.mem_KO.2 ⟨h1, ?_⟩⟩
  convert h2 using 2
  group
private theorem quot_finite (d : Fin n → kˣ) :
    Finite ((glIwa k n).N ⧸ ((glIwa k n).Nconj (Sig.dg d)).subgroupOf (glIwa k n).N) := by
  classical
  let V := Sig.Lev.iw k
  have hI : HeckePair (V.J n) := ((Sig.finFacts k V).2.2.2.2.2 n).1
  have hT : (Sig.dg d)⁻¹ ∈ (glIwa k n).Tf := inv_mem ⟨d, rfl⟩
  have hfin : Finite (MulAction.orbit (V.J n) ((Sig.dg d : GL (Fin n) k) : GL (Fin n) k ⧸ V.J n)) := (hI _).to_subtype
  refine Finite.of_injective
    (fun q : (glIwa k n).N ⧸ ((glIwa k n).Nconj (Sig.dg d)).subgroupOf (glIwa k n).N =>
      (⟨(((q.out : (glIwa k n).N) : GL (Fin n) k) * Sig.dg d : GL (Fin n) k), ⟨⟨q.out, V.N_le q.out.2⟩, rfl⟩⟩ :
        MulAction.orbit (V.J n) ((Sig.dg d : GL (Fin n) k) : GL (Fin n) k ⧸ V.J n))) ?_
  intro q q' h
  have h1 : ((((q.out : (glIwa k n).N) : GL (Fin n) k) * Sig.dg d : GL (Fin n) k) : GL (Fin n) k ⧸ V.J n) =
      (((q'.out : (glIwa k n).N) : GL (Fin n) k) * Sig.dg d : GL (Fin n) k) := congrArg Subtype.val h
  have h2 := QuotientGroup.eq.1 h1
  set z : GL (Fin n) k := ((q.out : (glIwa k n).N) : GL (Fin n) k)⁻¹ * (q'.out : (glIwa k n).N) with hz
  have hzN : z ∈ (glIwa k n).N := mul_mem (inv_mem q.out.2) q'.out.2
  have h3 : (Sig.dg d)⁻¹ * z * Sig.dg d ∈ V.J n := by
    convert h2 using 1
    rw [hz]
    group
  have h4 : (Sig.dg d)⁻¹ * z * Sig.dg d ∈ (glIwa k n).N := by
    have := (glIwa k n).Tf_Nf _ hT z ((glIwa k n).N_le hzN)
    rw [inv_inv] at this
    exact ⟨this, V.J_le_KO h3⟩
  have h5 : z ∈ (glIwa k n).Nconj (Sig.dg d) :=
    ⟨_, h4, by
      change Sig.dg d * ((Sig.dg d)⁻¹ * z * Sig.dg d) * (Sig.dg d)⁻¹ = z
      group⟩
  have h6 : (QuotientGroup.mk q.out : (glIwa k n).N ⧸ ((glIwa k n).Nconj (Sig.dg d)).subgroupOf (glIwa k n).N) =
      QuotientGroup.mk q'.out := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [hz] using h5
  rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h6
private theorem reps (d : Fin n → kˣ) : ∃ s : Finset (GL (Fin n) k), (∀ u ∈ s, u ∈ (glIwa k n).N) ∧
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ (GL (Fin n) k) M) (v : M),
      (glIwa k n).uOp ρ (Sig.dg d) v = ∑ u ∈ s, ρ u (ρ (Sig.dg d) v) := by
  classical
  haveI := quot_finite d
  letI : Fintype ((glIwa k n).N ⧸ ((glIwa k n).Nconj (Sig.dg d)).subgroupOf (glIwa k n).N) := Fintype.ofFinite _
  have hinj : Function.Injective fun q : (glIwa k n).N ⧸ ((glIwa k n).Nconj (Sig.dg d)).subgroupOf (glIwa k n).N =>
      ((q.out : (glIwa k n).N) : GL (Fin n) k) := fun q q' h => by
    have h1 : q.out = q'.out := Subtype.ext h
    have h2 := congrArg (QuotientGroup.mk : (glIwa k n).N → (glIwa k n).N ⧸ ((glIwa k n).Nconj (Sig.dg d)).subgroupOf (glIwa k n).N) h1
    rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h2
  refine ⟨Finset.univ.image fun q : (glIwa k n).N ⧸ ((glIwa k n).Nconj (Sig.dg d)).subgroupOf (glIwa k n).N =>
      ((q.out : (glIwa k n).N) : GL (Fin n) k), fun u hu => ?_, fun M _ _ ρ v => ?_⟩
  · obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
    exact q.out.2
  · rw [Finset.sum_image (fun x _ y _ h => hinj h), Iwa.uOp, finsum_eq_sum_of_fintype, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_mul, Module.End.mul_apply]
private theorem idx {d : Fin n → kˣ} (hd : Dom d) {s : Finset (GL (Fin n) k)}
    (hs : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ (GL (Fin n) k) M) (v : M),
      (glIwa k n).uOp ρ (Sig.dg d) v = ∑ u ∈ s, ρ u (ρ (Sig.dg d) v)) :
    (s.card : ℂ) = (((deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) d))⁻¹ : ℂˣ) : ℂ) *
      (((deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) d))⁻¹ : ℂˣ) : ℂ) := by
  let ρ₀ : Representation ℂ (GL (Fin n) k) ℂ := Representation.trivial ℂ _ ℂ
  have hq : IsUnit (resCard k : ℂ) := (Nat.cast_ne_zero.2 (Nat.card_pos (α := 𝓀[k])).ne').isUnit
  obtain ⟨θ, hθ, -⟩ := thetaEx k n ⊤ ℂ ℂ ρ₀ hq
  let w : fixd ρ₀ (iwC k n ⊤) := ⟨1, fun _ _ => by simp [ρ₀]⟩
  have h := jqTheta k n ⊤ ℂ ρ₀ θ hθ d w
  have hJ : (Sig.Lev.iw k).J n = iwC k n ⊤ := (Sig.link k n).1
  have hU := (Sig.hkMul k (Sig.Lev.iw k) n ℂ ρ₀).2 d hd
  rw [hJ] at hU
  have hU' : (((θ d : Module.End ℂ (fixd ρ₀ (iwC k n ⊤))) w : ℂ)) = s.card := by
    rw [hθ d hd]
    refine (hU w).trans ?_
    rw [hs ℂ ρ₀]
    simp [ρ₀, w]
  have hker : twKer ρ₀ (unipB k (Fin n)) 1 = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, v, rfl⟩ := hy
      simp [ρ₀]
    | zero => rfl
    | add a b _ _ ha hb => rw [ha, hb, add_zero]
    | smul a y _ hy => rw [hy, smul_zero]
  have e1 : ρ₀ (diagT k (Fin n) d) (w : ℂ) = w := by simp [ρ₀]
  rw [hU', UnramFixed.jacB_apply, jacBU_mk, e1, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.eq, hker, Submodule.mem_bot, sub_eq_zero] at h
  rw [h]
  simp [w]
private theorem jac_eig {T : Type} [AddCommGroup T] [Module ℂ T] (V : Sig.Lev k) (ψ : Fin n → kˣ →* ℂˣ)
    (τ : Representation ℂ (GL (Fin n) k) T) {v : T} (hvJ : v ∈ fixd τ (V.J n)) {d : Fin n → kˣ} (hd : Sig.SDom d)
    (h : dc τ (V.J n) (V.J n) (Sig.dg d) v = Dict.expo ψ d • v) :
    jacB τ d (Submodule.Quotient.mk v : Jacquet τ (unipB k (Fin n))) =
      (torusChar ψ d : ℂ) • (Submodule.Quotient.mk v : Jacquet τ (unipB k (Fin n))) := by
  have hD : Dom d := fun i j hij => by
    rcases hij.eq_or_lt with rfl | h
    · exact le_rfl
    · exact (hd i j h).le
  obtain ⟨s, hsN, hs⟩ := reps (k := k) (n := n) d
  let w : fixd τ (V.J n) := ⟨v, hvJ⟩
  have hI : HeckePair (V.J n) := ((Sig.finFacts k V).2.2.2.2.2 n).1
  have h1 := (hkApply ℂ _ T τ _ _ (Sig.dg d) (hI (Sig.dg d))).1 w
  have h2 := (Sig.hkMul k V n T τ).2 d hD w
  have h3 : ∑ u ∈ s, τ u (τ (Sig.dg d) v) = Dict.expo ψ d • v := (hs T τ v).symm.trans (h2.symm.trans (h1.trans h))
  have h4 : (Submodule.Quotient.mk (∑ u ∈ s, τ u (τ (Sig.dg d) v)) : Jacquet τ (unipB k (Fin n))) =
      (s.card : ℂ) • (Submodule.Quotient.mk (τ (Sig.dg d) v) : Jacquet τ (unipB k (Fin n))) := by
    rw [← Submodule.mkQ_apply, map_sum, Nat.cast_smul_eq_nsmul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact sub_mem_twKer (π := τ) (hsN u hu).1 _
  have e := idx hD hs
  rw [h3, e, Submodule.Quotient.mk_smul] at h4
  rw [UnramFixed.jacB_apply, jacBU_mk]
  set c : ℂ := (((deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) d))⁻¹ : ℂˣ) : ℂ) with hc
  have hc0 : c ≠ 0 := Units.ne_zero _
  have hx : Dict.expo ψ d = (torusChar ψ d : ℂ) * c := by
    rw [Dict.expo, Units.val_mul]
    rfl
  change c • (Submodule.Quotient.mk (τ (Sig.dg d) v) : Jacquet τ (unipB k (Fin n))) = _
  rw [hx, mul_comm, mul_smul, mul_smul] at h4
  exact (smul_cancel hc0 h4).symm
private theorem mk_ne {T : Type} [AddCommGroup T] [Module ℂ T] (V : Sig.Lev k) (τ : Representation ℂ (GL (Fin n) k) T)
    (hτ : IsSmooth τ) {v : T} (hv0 : v ≠ 0) (hvJ : v ∈ fixd τ (V.J n)) (e : (Fin n → kˣ) → ℂ) (he : ∀ d, e d ≠ 0)
    (hE : ∀ d, Sig.SDom d → dc τ (V.J n) (V.J n) (Sig.dg d) v = e d • v) :
    (Submodule.Quotient.mk v : Jacquet τ (unipB k (Fin n))) ≠ 0 := by
  intro hv
  have h1 : v ∈ twKer τ (unipB k (Fin n)) 1 := (Submodule.Quotient.mk_eq_zero _).1 hv
  obtain ⟨c, hc⟩ := valuation_surjective (uniformizer k)
  have hc0 : c ≠ 0 := fun h => by
    rw [h, map_zero] at hc
    exact GlobalTheory.IwahoriInj.unif_pos.ne hc
  have hx : valuation k ((Units.mk0 c hc0 : kˣ) : k) = uniformizer k := hc
  generalize Units.mk0 c hc0 = x at hx
  have hle : unipO k n ≤ V.J n := V.N_le
  have h2 : ∀ w ∈ twKer τ (unipB k (Fin n)) 1, ∀ᶠ m : ℕ in Filter.atTop,
      τ (diagT k (Fin n) (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ))))) w ∈ twKer τ (V.J n) 1 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, w, rfl⟩ := hy
      filter_upwards [jqInj_ev hx u.2] with m hm
      have := GlobalTheory.IwahoriInj.sub_mem_twKer (π := τ) (hle hm)
        (τ (diagT k (Fin n) (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ))))) w)
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply, ← map_sub] at this
      simpa only [MonoidHom.one_apply, Units.val_one, one_smul] using this
    | zero => simp
    | add a b _ _ ha hb =>
      filter_upwards [ha, hb] with m h1 h2
      rw [map_add]
      exact add_mem h1 h2
    | smul a y _ hy =>
      filter_upwards [hy] with m h1
      rw [map_smul]
      exact Submodule.smul_mem _ a h1
  obtain ⟨m, hm, hm1⟩ := ((h2 _ h1).and (Filter.eventually_gt_atTop 0)).exists
  have hd := jqInj_dom (n := n) hx m
  have hsd : Sig.SDom (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ)))) := by
    intro i j hij
    simp only [Units.val_zpow_eq_zpow_val, map_zpow₀, hx]
    refine (zpow_lt_zpow_iff_right_of_lt_one₀ unif_pos uniformizer_lt_one).2 ?_
    have h3 : ((i : ℕ) : ℤ) + 1 ≤ (j : ℕ) := by exact_mod_cast Fin.lt_def.1 hij
    have h4 : (1 : ℤ) ≤ m := by exact_mod_cast hm1
    nlinarith
  obtain ⟨s, hsN, hs⟩ := reps (k := k) (n := n) (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ))))
  let w : fixd τ (V.J n) := ⟨v, hvJ⟩
  have hF := (Sig.finFacts k V).2.2.2.2.2 n
  have h3 := (hkApply ℂ _ T τ _ _ (Sig.dg fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ)))) (hF.1 _)).1 w
  have h4 := (Sig.hkMul k V n T τ).2 _ hd w
  have h5 : (hk τ (V.J n) (Sig.dg fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ)))) w : T) = 0 := by
    refine GlobalTheory.IwahoriInj.eq_zero_of_fixed hτ hF.2.2.1 (GlobalTheory.IwahoriInj.mem_fixed.2 (hk τ (V.J n) _ w).2) ?_
    rw [h4, hs T τ]
    refine Submodule.sum_mem _ fun u hu => ?_
    exact GlobalTheory.IwahoriInj.apply_mem_twKer (V.N_le (hsN u hu)) hm
  have h6 : e _ • v = 0 := ((hE _ hsd).symm.trans h3.symm).trans h5
  exact hv0 ((smul_eq_zero.1 h6).resolve_left (he _))
end Lev
theorem UpperTheory.V.Z.Sym.W.local_sub_d_statement :
    _root_.UpperTheory.V.Z.Sym.W.LocSubDAlt := by
  intro H k _ _ _ _ n V ψ hψ T _ _ τ hs hi v hv0 hvJ heig
  have hx : (Submodule.Quotient.mk v : Jacquet τ (unipB k (Fin n))) ≠ 0 :=
    mk_ne V τ hs hv0 hvJ (Dict.expo ψ) (fun d => Units.ne_zero _) heig
  have hsd := fun d (hd : Sig.SDom d) => jac_eig V ψ τ hvJ hd (heig d hd)
  have ht : ∀ t, jacB τ t (Submodule.Quotient.mk v : Jacquet τ (unipB k (Fin n))) =
      (torusChar ψ t : ℂ) • (Submodule.Quotient.mk v : Jacquet τ (unipB k (Fin n))) := by
    intro t
    obtain ⟨d, hd, htd⟩ := exists_sdom t
    have h1 := hsd d hd
    have h2 := hsd (t * d) htd
    rw [map_mul, Module.End.mul_apply, h1, map_smul, map_mul, Units.val_mul, mul_comm, mul_smul] at h2
    exact smul_cancel (Units.ne_zero (torusChar ψ d)) h2
  have hl : HasFiniteLength (jacB τ) :=
    (hasFiniteLength_comp_iff _ _ (leviTorus k (Fin n)).surjective).2
      ((H.loc.bz k).2.1 _ _ _ (points (Fin n)) _ τ hs (hasFiniteLength_of_isIrreducible hi))
  haveI := GlobalTheory.TorusEigenform.secondCountableTopology_units k
  obtain ⟨-, l, hl0, hle⟩ := exists_form (χ := torusChar ψ) (isSmooth_jacB hs) hl hx fun t =>
    ⟨1, by rw [pow_one, LinearMap.sub_apply, Module.algebraMap_end_apply, ht t, sub_self]⟩
  exact GlobalTheory.SatakeExists.isSubquotient_of_eigenform hs hi (torusChar ψ) l hl0 hle
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al
private theorem compD :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L], Unr L → ∀ n : ℕ, 1 ≤ n → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Submodule ℂ (UA L n → ℂ)), IsAutRepU π → ∀ w, IsSplitAt w → ∀ W : Sig.Lev (Kw w),
        ∀ φ : UA L n → V, φ ≠ 0 → CoefIn φ π → (∀ x ∈ locU n w, cLoc w x ∈ W.J n → ∀ g, φ (g * x) = φ g) →
        ∀ ψ : Fin n → (Kw w)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) → EigT φ w W ψ → CompSub π w ψ := by
  intro H L _ _ _ unr n hn V _ _ π hπ w hw W φ h0 hc hJ ψ hψ he
  obtain ⟨s1, s2, -⟩ := secSpec L n w hw
  obtain ⟨τ, hτ⟩ := _root_.UpperTheory.V.Z.Sym.Al.exists_local_component_at_split_of_unitary_aut H L unr n hn π hπ w hw
  obtain ⟨f, hf⟩ : ∃ f : V →ₗ[ℂ] ℂ, f ∘ φ ≠ 0 := by
    obtain ⟨g, hg⟩ := Function.ne_iff.1 h0
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero ℂ hg
    exact ⟨f, Function.ne_iff.2 ⟨g, hf⟩⟩
  obtain ⟨p, hp, hp0⟩ := (isoCopy _ _ _ τ.ρ _ τ.irred (isoTypic L n π hπ w hw τ hτ)).1 ⟨f ∘ φ, hc f⟩ fun h => hf (congrArg Subtype.val h)
  refine ⟨hψ, τ, hτ, _root_.UpperTheory.V.Z.Sym.W.local_sub_d_statement H _ n W ψ hψ _ τ.ρ τ.smooth τ.irred _ hp0 (fun u hu => ?_) fun d hd => ?_⟩
  · rw [← hp]
    congr 1
    exact Subtype.ext (funext fun g => congrArg f (hJ _ (s1 u) (by rwa [s2]) g))
  · rw [← dcMap W _ τ.ρ p hp, ← map_smul]
    congr 1
    apply Subtype.ext
    have a := dcMap W ((repOn hπ).comp (secW n w)) ((RU L n).comp (secW n w)) π.subtype (fun _ _ => rfl) (Sig.dg d) ⟨f ∘ φ, hc f⟩
    have b := dcMap W ((rightReg ℂ (UA L n) V).comp (secW n w)) ((RU L n).comp (secW n w)) (f.compLeft (UA L n))
      (fun _ _ => rfl) (Sig.dg d) φ
    rw [show UpperTheory.V.Hi.dc _ _ _ _ φ = _ • φ from he d hd, map_smul] at b
    exact a.trans b.symm
private theorem mem_lev {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {U : Subgroup (UA L n)} {S : Finset (Plc L)}
    (hS : Places (S : Set (Plc L))) (hK : ∀ w ∈ S, locU n w ⊓ Kall L n ≤ U) {w : Plc L} (hw : w ∈ S) {x : UA L n}
    (hx : x ∈ locU n w) (hJ : cLoc w x ∈ (iw w).J n) : x ∈ lev U S iw := by
  have hk : x ∈ Kall L n := by
    refine ((factor L n w).2.2.2.2.1 x hx).2 ?_
    rw [← GlobalTheory.HeckeEigConj.KO_eq_KGL]
    exact ((Sig.finFacts _ (iw w)).2.2.2.2.2 n).2.2.2 hJ
  simp only [lev, Subgroup.mem_inf, Subgroup.mem_iInf]
  refine ⟨hK w hw ⟨hx, hk⟩, fun w' hw' => ?_⟩
  by_cases e : w' = w
  · subst e; exact hJ
  · have hne : w.under (𝓞 (Lp L)) ≠ w'.under (𝓞 (Lp L)) := fun h => e (hS.inj hw' hw h.symm)
    have := (factor L n w').2.2.1 w hne hx
    simp only [away, Subgroup.mem_iInf] at this
    rw [Subgroup.mem_comap, (MonoidHom.mem_ker.1 (this w' rfl))]
    exact one_mem _
private theorem mem_level_of_local_depth {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {S₀ S : Finset (Plc L)} {c : ℕ}
    (hS : Places ((S₀ : Set (Plc L)) ∪ S)) (hd : Disjoint S₀ S) {w : Plc L} (hw : w ∈ S₀) {x : UA L n}
    (hx : x ∈ locU n w) (hJ : cLoc w x ∈ (deep c w).J n) : x ∈ lev (lev (Kall L n) S₀ (deep c)) S iw := by
  have hk : x ∈ Kall L n := by
    refine ((factor L n w).2.2.2.2.1 x hx).2 ?_
    rw [← GlobalTheory.HeckeEigConj.KO_eq_KGL]
    exact ((Sig.finFacts _ (deep c w)).2.2.2.2.2 n).2.2.2 hJ
  have key : ∀ w' ∈ (S₀ : Set (Plc L)) ∪ S, w' ≠ w → cLoc w' x = 1 := fun w' hw' e => by
    have hne : w.under (𝓞 (Lp L)) ≠ w'.under (𝓞 (Lp L)) := fun h => e (hS.inj hw' (Or.inl hw) h.symm)
    have := (factor L n w').2.2.1 w hne hx
    simp only [away, Subgroup.mem_iInf] at this
    exact MonoidHom.mem_ker.1 (this w' rfl)
  simp only [lev, Subgroup.mem_inf, Subgroup.mem_iInf]
  refine ⟨⟨hk, fun w' hw' => ?_⟩, fun w' hw' => ?_⟩
  · by_cases e : w' = w
    · subst e; exact hJ
    · rw [Subgroup.mem_comap, key w' (Or.inl hw') e]
      exact one_mem _
  · rw [Subgroup.mem_comap, key w' (Or.inr hw') fun e => Finset.disjoint_left.1 hd hw (e ▸ hw')]
    exact one_mem _
private theorem outW :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L], Unr L → ∀ n : ℕ, 1 ≤ n → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V), ContCoef R → ∀ (S₀ : Finset (Plc L)) (c : ℕ) (U : Subgroup (UA L n)), U = lev (Kall L n) S₀ (deep c) → IsLevel U →
        ∃ A : Set (Submodule ℂ (UA L n → ℂ)), A.Finite ∧ (∀ σ ∈ A, IsAutRepU σ ∧ (∃ φ ∈ σ, φ ≠ 0 ∧ ∀ u ∈ U, RU L n u φ = φ)) ∧
          ∀ S : Finset (Plc L), Places ((S₀ : Set (Plc L)) ∪ S) → Disjoint S₀ S → Places (S : Set (Plc L)) → (∀ w ∈ S, locU n w ⊓ Kall L n ≤ U) →
          ∀ (ψ : ∀ w : Plc L, Fin n → (Kw w)ˣ →* ℂˣ) (φ : UA L n → V), φ ≠ 0 → IsAF R (lev U S iw) φ →
          (∀ w ∈ S, (∀ i, ∀ u ∈ UpperTheory.V.Hi.Uo (Kw w), ψ w i u = 1) ∧ (∀ i i', i ≠ i' → ψ w i ≠ ψ w i' ∧ ψ w i ≠ ψ w i' * absPow (Kw w) 1) ∧
            EigT φ w (iw w) (ψ w)) → (∀ w ∈ S₀, (∀ i, IsSmoothChar (ψ w i)) ∧ EigT φ w (deep c w) (ψ w)) →
          ∃ σ ∈ A, (∀ w ∈ S₀, CompSub σ w (ψ w)) ∧ ∀ w ∈ S, CompSub σ w (ψ w) := by
  intro H L _ _ _ unr n hn V _ _ _ R hR S₀ c U eU hU
  obtain ⟨A, hA, hA', h⟩ := UpperTheory.V.Z.Sym.U.finFamU L n V R hR U hU
  refine ⟨A, hA, hA', fun S hP hd hS hK ψ φ h0 hφ hψ hψ0 => ?_⟩
  obtain ⟨π, φ₁, hπ, h1, hφ₁, hc, he⟩ := proj L n V R hR _ ((cof L n).2.2.1 U hU S iw) φ h0 hφ
  have hcs : ∀ w ∈ S, CompSub π w (ψ w) := fun w hw =>
    _root_.UpperTheory.V.Z.Sym.Al.comp_sub_of_eigen_vector_fixed_by_j H L unr n hn V π hπ w (hS.split w hw) φ₁ h1 hc (fun x hx hJ => hφ₁.level x (mem_lev hS hK hw hx hJ)) (ψ w)
      (fun i => (unrSmooth _).1 _ ((hψ w hw).1 i)) fun d hd => he _ _ _ _ ((hψ w hw).2.2 d hd)
  have hc0 : ∀ w ∈ S₀, CompSub π w (ψ w) := fun w hw =>
    compD H L unr n hn V π hπ w (hP.split w (Or.inl hw)) (deep c w) φ₁ h1 hc
      (fun x hx hJ => hφ₁.level x (eU ▸ mem_level_of_local_depth hP hd hw hx hJ)) (ψ w) (hψ0 w hw).1 fun d hd => he _ _ _ _ ((hψ0 w hw).2 d hd)
  obtain ⟨φ₂, h2, hc2, hφ₂⟩ := raise L n V R π hπ U hU.1 S hS
    (fun w hw => ⟨hK w hw, _root_.UpperTheory.V.Z.Sym.Al.unramified_of_split_distinct_characters H L n π w (ψ w) (hS.split w hw) (hcs w hw) (hψ w hw).1 (hψ w hw).2.1⟩) iw φ₁ h1 hc hφ₁
  obtain ⟨σ, hσ, ht⟩ := h π hπ φ₂ h2 hφ₂ hc2
  refine ⟨σ, hσ, fun w hw => ?_, fun w hw => ?_⟩
  · obtain ⟨a, τ, b, c⟩ := hc0 w hw
    exact ⟨a, τ, ht w τ b, c⟩
  · obtain ⟨a, τ, b, c⟩ := hcs w hw
    exact ⟨a, τ, ht w τ b, c⟩
private theorem smo {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ψ : Fin 2 → kˣ →* ℂˣ}
    (h : ∀ i, IsSmoothChar (ψ i)) : ∀ i, IsSmoothChar ((![ψ 0 / ψ 1, 1, (ψ 0 / ψ 1)⁻¹] : Fin 3 → kˣ →* ℂˣ) i) := by
  have h1 : IsSmoothChar (ψ 0 / ψ 1) := by
    rw [div_eq_mul_inv]
    exact (h 0).mul (h 1).inv
  intro i
  fin_cases i
  · exact h1
  · have := h1.mul h1.inv
    rwa [mul_inv_cancel] at this
  · exact h1.inv
private theorem unram_of {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (σ : Submodule ℂ (UA L n → ℂ)) (S : Finset (Plc L))
    (V : ∀ w : Plc L, Sig.Lev (Kw w)) (h : ∃ φ ∈ σ, φ ≠ 0 ∧ ∀ u ∈ lev (Kall L n) S V, RU L n u φ = φ) (w : Plc L)
    (hw : ∀ w' ∈ S, w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))) : IsUnramU σ w := by
  obtain ⟨φ, h1, h2, h3⟩ := h
  refine ⟨φ, h1, h2, fun x hx hK => h3 x ?_⟩
  simp only [lev, Subgroup.mem_inf, Subgroup.mem_iInf]
  refine ⟨((factor L n w).2.2.2.2.1 x hx).2 hK, fun w' hw' => ?_⟩
  have := (factor L n w').2.2.1 w (hw w' hw').symm hx
  simp only [away, Subgroup.mem_iInf] at this
  rw [Subgroup.mem_comap, (MonoidHom.mem_ker.1 (this w' rfl))]
  exact one_mem _
private theorem pigeon {X I : Type} (A : Set X) (hA : A.Finite) (P : X → I → Prop)
    (h : ∀ S : Finset I, ∃ x ∈ A, ∀ i ∈ S, P x i) : ∃ x ∈ A, ∀ i, P x i := by
  classical
  by_contra hn
  push Not at hn
  choose f hf using fun x : A => hn x.1 x.2
  haveI := hA.fintype
  obtain ⟨x, hx, h1⟩ := h (Finset.univ.image f)
  exact hf ⟨x, hx⟩ (h1 _ (Finset.mem_image_of_mem f (Finset.mem_univ _)))
theorem UpperTheory.V.Z.Sym.W.adjoint_lift_w_of_literal_automorphy_spec_out : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → UpperTheory.V.Z.Sym.W.SpecOutS → UpperTheory.V.Z.Sym.W.AdLiftW := by
  classical
  intro H hS L _ _ _ unr S₀ P hdis hpl htwo π hπ j hj hwt hunr ψ hψ hP
  have mono : ∀ {T : Set (Plc L)}, T ⊆ (S₀ : Set (Plc L)) ∪ P → Places T := fun h =>
    ⟨fun w hw => hpl.split w (h hw), hpl.inj.mono h⟩
  obtain ⟨c₀, hc₀⟩ := hS L unr S₀ (mono Set.subset_union_left) htwo j hj
  have hd : ∀ p : S₀ × Fin 2, ∃ c₁ : ℕ, ∀ c ≥ c₁, ∀ u ∈ UpperTheory.V.Hi.Uc (Kw p.1.1) (c + 1), ψ p.1.1 p.2 u = 1 := fun p =>
    smoothDepth _ _ ((hψ p.1.1 (Or.inl p.1.2)).1 p.2)
  choose c₁ hc₁ using hd
  obtain ⟨c, hc, hc'⟩ : ∃ c, c₀ ≤ c ∧ ∀ p, c₁ p ≤ c :=
    ⟨max c₀ (Finset.univ.sup c₁), le_max_left _ _, fun p => (Finset.le_sup (Finset.mem_univ p)).trans (le_max_right _ _)⟩
  obtain ⟨U₂, hU₂, hm⟩ := hc₀ c hc
  obtain ⟨⟨f3, c3⟩, -⟩ := contE (InfinitePlace L) j
  obtain ⟨-, f2, c2⟩ := contE (InfinitePlace L) (2 * j + 1)
  have hU₃ : IsLevel (lev (Kall L 3) S₀ (deep c)) := (cof L 3).2.2.1 _ (cof L 3).2.1 _ _
  obtain ⟨A₃, hA₃, hA₃', h₃⟩ := outW H L unr 3 (by norm_num) _ _ c3 S₀ c _ rfl hU₃
  obtain ⟨A₂, hA₂, hA₂', h₂⟩ := _root_.UpperTheory.V.Z.Sym.Al.outRep_alt H L unr 2 (by norm_num) _ _ (c2 0) _ hU₂
  let Gd : Plc L → Prop := fun w => locU 2 w ⊓ Kall L 2 ≤ U₂ ∧ locU 3 w ⊓ Kall L 3 ≤ lev (Kall L 3) S₀ (deep c)
  have hG : ∀ᶠ w in Filter.cofinite, Gd w := ((cof L 2).2.2.2 _ hU₂).and ((cof L 3).2.2.2 _ hU₃)
  let Q : Submodule ℂ (UA L 3 → ℂ) ⊕ Submodule ℂ (UA L 2 → ℂ) → Plc L → Prop := fun x w =>
    x.elim (fun σ => CompSub σ w ![ψ w 0 / ψ w 1, 1, (ψ w 0 / ψ w 1)⁻¹])
      fun σ => ∃ ψ', CompSub σ w ψ' ∧ ψ' 0 / ψ' 1 = (ψ w 0 / ψ w 1) ^ 2
  obtain ⟨x, hx, hQ⟩ := pigeon (I := {w // w ∈ P ∧ Gd w}) (Sum.inl '' {σ ∈ A₃ | ∀ w ∈ S₀, CompSub σ w ![ψ w 0 / ψ w 1, 1, (ψ w 0 / ψ w 1)⁻¹]} ∪ Sum.inr '' A₂) (((hA₃.subset (Set.sep_subset _ _)).image _).union (hA₂.image _))
    (fun x w => Q x w.1) fun S => by
      let S₁ : Finset (Plc L) := S.image Subtype.val
      have h1 : ∀ w ∈ S₁, w ∈ P ∧ Gd w := fun w hw => by
        obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hw
        exact y.2
      have hn : ∀ w ∈ S₁, w ∉ S₀ := fun w hw h => Set.disjoint_left.1 hdis h (h1 w hw).1
      have hsub : ((S₀ : Set (Plc L)) ∪ S₁) ⊆ (S₀ : Set (Plc L)) ∪ P := Set.union_subset_union_right _ fun w hw => (h1 w hw).1
      have hp1 : Places (S₁ : Set (Plc L)) := mono fun w hw => Or.inr (h1 w hw).1
      let W : ∀ w : Plc L, Sig.Lev (Kw w) := fun w => if w ∈ S₀ then deep c w else iw w
      have W0 : ∀ w ∈ S₀, W w = deep c w := fun w hw => if_pos hw
      have W1 : ∀ w ∈ S₁, W w = iw w := fun w hw => if_neg (hn w hw)
      obtain ⟨e, φ, h0, hAF, hE⟩ := _root_.UpperTheory.V.Z.Sym.Al.inVec_alt H L π hπ j hwt (S₀ ∪ S₁) (by rw [Finset.coe_union]; exact mono hsub)
        (fun w hw => hunr w fun w' hw' => hw w' (Finset.mem_union_left _ hw')) W ψ fun w hw => by
          rcases Finset.mem_union.1 hw with hw | hw
          · exact ⟨hψ w (Or.inl hw), fun i => by rw [W0 w hw]; exact hc₁ (⟨w, hw⟩, i) c (hc' _)⟩
          · exact ⟨hψ w (Or.inr (h1 w hw).1), fun i => by rw [W1 w hw]; exact (hP w (h1 w hw).1).1 i⟩
      have hle : lev (lev (Kall L 2) S₀ (deep c)) S₁ iw ≤ lev (Kall L 2) (S₀ ∪ S₁) W := by
        intro u hu
        simp only [lev, Subgroup.mem_inf, Subgroup.mem_iInf] at hu ⊢
        refine ⟨hu.1.1, fun w hw => ?_⟩
        rcases Finset.mem_union.1 hw with hw | hw
        · rw [W0 w hw]; exact hu.1.2 w hw
        · rw [W1 w hw]; exact hu.2 w hw
      rcases hm S₁ (Finset.disjoint_right.2 hn) (mono hsub) (fun w hw => (h1 w hw).2.1) (fun w => ψ w 0 / ψ w 1) e φ h0
        ⟨hAF.left, hAF.inf, fun u hu => hAF.level u (hle hu)⟩
        (fun w hw => eigTS L _ φ w _ _ (W0 w hw ▸ hE w (Finset.mem_union_left _ hw)))
        (fun w hw => eigTS L _ φ w _ _ (W1 w hw ▸ hE w (Finset.mem_union_right _ hw))) with ⟨φ', a0, a1, a3, a2⟩ | ⟨φ', a0, a1, a2⟩
      · obtain ⟨σ, hσ, hs0, hs⟩ := h₃ S₁ (mono hsub) (Finset.disjoint_right.2 hn) hp1 (fun w hw => (h1 w hw).2.2) (fun w => ![ψ w 0 / ψ w 1, 1, (ψ w 0 / ψ w 1)⁻¹]) φ' a0 a1
          (fun w hw => ⟨(regUnl _ _ (hP w (h1 w hw).1).2).1.1, (regUnl _ _ (hP w (h1 w hw).1).2).1.2, a2 w hw⟩)
          fun w hw => ⟨smo (hψ w (Or.inl hw)).1, a3 w hw⟩
        exact ⟨.inl σ, Or.inl ⟨σ, ⟨hσ, hs0⟩, rfl⟩, fun i hi => hs i.1 (Finset.mem_image_of_mem _ hi)⟩
      · obtain ⟨φ'', ψ', b0, b1, b2⟩ := UpperTheory.V.Z.Sym.Al.refine L _ _ U₂ hU₂ S₁ hp1 (fun w hw => (h1 w hw).2.1) _ φ' a0 a1 a2
        obtain ⟨σ, hσ, hs⟩ := h₂ S₁ hp1 (fun w hw => (h1 w hw).2.1) ψ' φ'' b0 b1
          fun w hw => ⟨(b2 w hw).1, (regUnl _ _ (hP w (h1 w hw).1).2).2 _ (b2 w hw).2.1, (b2 w hw).2.2⟩
        exact ⟨.inr σ, Or.inr ⟨σ, hσ, rfl⟩, fun i hi =>
          ⟨ψ' i.1, hs i.1 (Finset.mem_image_of_mem _ hi), (b2 i.1 (Finset.mem_image_of_mem _ hi)).2.1⟩⟩
  rcases hx with ⟨σ, hσ, rfl⟩ | ⟨σ, hσ, rfl⟩
  · exact Or.inl ⟨σ, (hA₃' σ hσ.1).1, unram_of _ _ _ (hA₃' σ hσ.1).2, hσ.2, hG.mono fun w hw hw' => hQ ⟨w, hw', hw⟩⟩
  · exact Or.inr ⟨σ, hA₂' σ hσ, hG.mono fun w hw hw' => hQ ⟨w, hw', hw⟩⟩
end
end
