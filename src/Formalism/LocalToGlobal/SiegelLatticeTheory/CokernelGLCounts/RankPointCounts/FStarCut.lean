import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefCutDeep
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.XPEqZzp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountOrb
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IdxRatioConjOfUnimod
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.IsOpenAddSubgroup
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsLoOfIntLow
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrGlobPOfInt

section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut
  Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem orbR_stable {p : PlF D} (Z0 : MP p) :
    ∀ Z ∈ Formalism.L2.SG.Pf.LocOrbSumPf.orbR (M p) Z0, ∀ l ρ, Formalism.MainNotions.S.TieN.IntLow (M p) l → Formalism.MainNotions.S.TieN.IntUp (M p) ρ →
      l * Z * ρ ∈ Formalism.L2.SG.Pf.LocOrbSumPf.orbR (M p) Z0 := by
  rintro Z ⟨l', ρ', hl', hρ', rfl⟩ l ρ hl hρ
  refine ⟨l * l', ρ' * ρ, Formalism.L2.SG.Pf.LocOrbCut.intLow_mul (M p) hl hl', Formalism.L2.SG.Pf.LocOrbCut.intUp_mul (M p) hρ' hρ, ?_⟩
  simp only [Matrix.mul_assoc]

theorem countAt_holds (γ : Formalism.L2.SG.TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D)
    (hE : Formalism.L2.SG.Pf.ZsVolCut.HypE M δ u u' F0 what₂ γ w F' L U) (p : PlF D) :
    CountAt M δ u u' w (hE.1 p) L U hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2.1
      (Formalism.L2.SG.LsDatumB.wtL M δ (D.mem u).A.T (D.mem u').A.T p w
        (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * Formalism.L2.SG.LsDatumB.sgnP p)) := by
  have hA := hE.1 p
  have hL := hE.2.2.2.2.2.2.2.1
  have hU := hE.2.2.2.2.2.2.2.2.1
  have heq := hE.2.2.2.2.2.2.2.2.2
  obtain ⟨a, ha⟩ := Formalism.L2.SG.Pf.PCount.modPt_full (δ := δ) (D.mem u).A.T (D.mem u').A.T p hA.2.1 w
  obtain ⟨πa, hD, hker⟩ := blockRetr_holds M a
  have hB := baseAt_holds M δ u u' w p hE.1 a ha
  have hInt := int_zzp M δ u u' F0 what₂ γ w F' L U hE p
  have hgW : ((gU M δ u u' w hA L U hL hU a hB : UP p) : GG p) • a.mat =
      Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * Formalism.L2.SG.LsDatumB.sgnP p +
        Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w := by
    rw [gU_smul, XP_eq_ZZP M δ u u' F0 hA w F' L U hL hU heq]
    rfl
  obtain ⟨hfin, hwt⟩ := Formalism.L2.SG.Pf.Coef.wtL_count M δ hA.1 ha hInt
  have hcard := card_cellRel M a πa hker (gU M δ u u' w hA L U hL hU a hB)
  rw [hgW] at hcard
  set Z0 : MP p := Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * Formalism.L2.SG.LsDatumB.sgnP p +
    Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w with hZ0
  have hcos := Formalism.L2.SG.Pf.Coef.cellCos (M p) a (Formalism.L2.SG.Pf.LocOrbSumPf.orbR (M p) Z0) (orbR_stable M Z0)
  refine countAt_of_parts M δ u u' w hA L U hL hU a hB πa hD _ ?_ ?_
  · rw [hcard, ← hcos, hwt]
  · rw [Nat.card_ne_zero]
    refine ⟨⟨Quotient.mk _ (CountAb.toCell a.mat (MulAction.stabilizer (UP p) a.mat) πa.ker (KU M p) πa
      (gU M δ u u' w hA L U hL hU a hB) hD 1)⟩, ?_⟩
    have hcl := (Formalism.L2.SG.Pf.Coef.cellCos_finite_iff (M p) a (Formalism.L2.SG.Pf.LocOrbSumPf.orbR (M p) Z0)
      (orbR_stable M Z0)).1 hfin
    have hrange := fC_range M a πa hker (gU M δ u u' w hA L U hL hU a hB)
    rw [hgW] at hrange
    rw [← hrange] at hcl
    have hinj : Function.Injective (Set.rangeFactorization (fC M a πa hker (gU M δ u u' w hA L U hL hU a hB))) :=
      fun x y h => fC_inj M a πa hker _ (congrArg Subtype.val h)
    exact @Finite.of_injective _ _ hcl.to_subtype _ hinj

end Formalism.L2.SG.Pf.CountAt
end
end

section
noncomputable section

open ValuativeRel Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.ProdEP2Uni

section LocTop

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem topE (M : Loc.Model F E) : IsTopologicalRing E := by
  haveI := M.L.top
  haveI := M.L.free
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [M.L.rank]; norm_num)
  first
    | exact IsModuleTopology.isTopologicalRing F E
    | exact IsModuleTopology.topologicalRing F E

theorem t2E (M : Loc.Model F E) : T2Space E := by
  haveI := M.L.top
  haveI := M.L.free
  haveI : T2Space F := MainNotions.LocalModelPeriodLattices.nonarchimedean_local_field_t2 inferInstance
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [M.L.rank]; norm_num)
  let b := Module.Free.chooseBasis F E
  have hc : Continuous (b.equivFun : E → (Module.Free.ChooseBasisIndex F E → F)) :=
    IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
  exact T2Space.of_injective_continuous b.equivFun.injective hc

theorem int_mem {x : F} (h : IsIntegral 𝒪[F] x) : x ∈ 𝒪[F] := by
  first
    | exact (Valuation.integer.integers (ValuativeRel.valuation F)).mem_of_integral h
    | (obtain ⟨y, hy⟩ := (Valuation.integer.integers (ValuativeRel.valuation F)).mem_of_integral h
       rw [← hy]
       exact y.2)

theorem alg_int (x : 𝒪[F]) : algebraMap F E (x : F) = algebraMap 𝒪[F] E x := by
  first
    | rfl
    | exact (IsScalarTower.algebraMap_apply 𝒪[F] F E x).symm

private theorem R_eq_O_of_split_eq_none (M : Loc.Model F E) (hg : M.split = none) : M.R = M.L.O := by
  simp only [Loc.Model.R, hg]

private theorem mem_R_iff_of_split_eq_some (M : Loc.Model F E) (g : Loc.SplitG M.L) (hg : M.split = some g) (z : E) :
    z ∈ M.R ↔ ∃ a b : 𝒪[F], g.e z = ((a : F), (b : F)) ∧
      Ideal.Quotient.mk (Ideal.span {g.q}) a = Ideal.Quotient.mk (Ideal.span {g.q}) b := by
  simp only [Loc.Model.R, hg, Subring.mem_comap, Subring.mem_map]
  constructor
  · rintro ⟨⟨a, b⟩, hab, he⟩
    exact ⟨a, b, he.symm, RingHom.mem_eqLocus.mp hab⟩
  · rintro ⟨a, b, he, hab⟩
    exact ⟨(a, b), RingHom.mem_eqLocus.mpr hab, he.symm⟩

theorem alg_mem_R (M : Loc.Model F E) (a : 𝒪[F]) : algebraMap F E (a : F) ∈ M.R := by
  cases hg : M.split with
  | none =>
    rw [R_eq_O_of_split_eq_none M hg, M.L.O_def, alg_int]
    exact isIntegral_algebraMap
  | some g =>
    rw [mem_R_iff_of_split_eq_some M g hg]
    refine ⟨a, a, ?_, rfl⟩
    rw [AlgEquiv.commutes]
    first
      | rfl
      | simp

private theorem splitG_e_mem_integers_of_mem_O (L : Loc.LocE F E) (g : Loc.SplitG L) {z : E} (hz : z ∈ L.O) :
    (g.e z).1 ∈ 𝒪[F] ∧ (g.e z).2 ∈ 𝒪[F] := by
  have h1 : IsIntegral 𝒪[F] (g.e z) := ((L.O_def z).mp hz).map (g.e.toAlgHom.restrictScalars 𝒪[F])
  exact ⟨int_mem (h1.map ((AlgHom.fst F F F).restrictScalars 𝒪[F])),
    int_mem (h1.map ((AlgHom.snd F F F).restrictScalars 𝒪[F]))⟩

private theorem mem_O_of_mem_R (M : Loc.Model F E) {z : E} (hz : z ∈ M.R) : z ∈ M.L.O := by
  cases hg : M.split with
  | none =>
    rwa [R_eq_O_of_split_eq_none M hg] at hz
  | some g =>
    obtain ⟨a, b, he, -⟩ := (mem_R_iff_of_split_eq_some M g hg z).mp hz
    rw [M.L.O_def]
    have ha : IsIntegral 𝒪[F] (a : F) := (isIntegral_algebraMap : IsIntegral 𝒪[F] (algebraMap 𝒪[F] F a))
    have hb : IsIntegral 𝒪[F] (b : F) := (isIntegral_algebraMap : IsIntegral 𝒪[F] (algebraMap 𝒪[F] F b))
    have h1 : IsIntegral 𝒪[F] (((a : F), (b : F)) : F × F) := IsIntegral.pair ha hb
    have h2 := h1.map (g.e.symm.toAlgHom.restrictScalars 𝒪[F])
    rw [← he] at h2
    have e : (g.e.symm.toAlgHom.restrictScalars 𝒪[F]) (g.e z) = z := g.e.symm_apply_apply z
    rwa [e] at h2

theorem R_compact [CharZero F] (M : Loc.Model F E) : IsCompact (M.R : Set E) := by
  haveI := topE M
  have hO := (MainNotions.LocalModelPeriodLattices.O_top M.L).2.1
  have hRo : IsOpen (M.R : Set E) := PI.ProdFormulaE.ROpen.isOpen_R M
  have hRc : IsClosed (M.R : Set E) := M.R.toAddSubgroup.isClosed_of_isOpen hRo
  exact hO.of_isClosed_subset hRc (fun z hz => mem_O_of_mem_R M hz)

theorem R_denom (M : Loc.Model F E) (y : E) : ∃ a : 𝒪[F], a ≠ 0 ∧ algebraMap F E (a : F) * y ∈ M.R := by
  haveI := M.L.free
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [M.L.rank]; norm_num)
  haveI : Nontrivial E := by
    first
      | exact Module.nontrivial_of_finrank_pos (R := F) (by rw [M.L.rank]; norm_num)
      | exact Module.nontrivial_of_finrank_eq_succ M.L.rank
  haveI : IsFractionRing 𝒪[F] F := ValuationRing.instIsFractionRingInteger (ValuativeRel.valuation F)
  have hinj : ∀ x : 𝒪[F], algebraMap 𝒪[F] E x = 0 → x = 0 := by
    intro x hx
    rw [← alg_int] at hx
    exact Subtype.ext ((map_eq_zero_iff _ (algebraMap F E).injective).mp hx)
  have halg : IsAlgebraic 𝒪[F] y := by
    have hF : IsAlgebraic F y := (Algebra.IsIntegral.isIntegral (R := F) y).isAlgebraic
    exact (IsFractionRing.isAlgebraic_iff 𝒪[F] F E).mpr hF
  have hex : ∃ s : 𝒪[F], s ≠ 0 ∧ IsIntegral 𝒪[F] (algebraMap 𝒪[F] E s * y) := by
    first
      | (obtain ⟨z, s, hs, hz⟩ := exists_integral_multiple halg hinj
         exact ⟨s, hs, by rw [mul_comm, hz]; exact z.2⟩)
      | (obtain ⟨s, hs, hi⟩ := halg.exists_integral_multiple
         exact ⟨s, hs, by rwa [Algebra.smul_def] at hi⟩)
  obtain ⟨s, hs, hsi⟩ := hex
  have hsy : algebraMap F E (s : F) * y ∈ M.L.O := by
    rw [M.L.O_def, alg_int]
    exact hsi
  cases hg : M.split with
  | none =>
    exact ⟨s, hs, by rw [R_eq_O_of_split_eq_none M hg]; exact hsy⟩
  | some g =>
    refine ⟨g.q * s, mul_ne_zero g.q_irr.ne_zero hs, ?_⟩
    obtain ⟨h1, h2⟩ := splitG_e_mem_integers_of_mem_O M.L g hsy
    rw [mem_R_iff_of_split_eq_some M g hg]
    refine ⟨g.q * ⟨_, h1⟩, g.q * ⟨_, h2⟩, ?_, ?_⟩
    · have e : algebraMap F E ((g.q * s : 𝒪[F]) : F) * y =
          algebraMap F E (g.q : F) * (algebraMap F E (s : F) * y) := by
        rw [MulMemClass.coe_mul, map_mul, mul_assoc]
      rw [e, map_mul, AlgEquiv.commutes]
      ext <;> simp
    · have hq : ∀ t : 𝒪[F], Ideal.Quotient.mk (Ideal.span {g.q}) (g.q * t) = 0 := fun t =>
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right t _ (Ideal.mem_span_singleton_self _))
      rw [hq, hq]

theorem common_denom (M : Loc.Model F E) {ι : Type} [Fintype ι] (y : ι → E) :
    ∃ a : 𝒪[F], a ≠ 0 ∧ ∀ k, algebraMap F E (a : F) * y k ∈ M.R := by
  classical
  choose d hd0 hd using fun k => R_denom M (y k)
  refine ⟨∏ k, d k, Finset.prod_ne_zero_iff.mpr fun k _ => hd0 k, fun k => ?_⟩
  have hp : (∏ j, d j) = (∏ j ∈ Finset.univ.erase k, d j) * d k :=
    (Finset.prod_erase_mul _ _ (Finset.mem_univ k)).symm
  rw [hp]
  have e : algebraMap F E (((∏ j ∈ Finset.univ.erase k, d j) * d k : 𝒪[F]) : F) * y k =
      algebraMap F E ((∏ j ∈ Finset.univ.erase k, d j : 𝒪[F]) : F) * (algebraMap F E (d k : F) * y k) := by
    rw [MulMemClass.coe_mul, map_mul, mul_assoc]
  rw [e]
  exact M.R.mul_mem (alg_mem_R M _) (hd k)

end LocTop

end Formalism.L2.SG.Pf.ProdEP2Uni
end
end

section
noncomputable section

open scoped Classical
open NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape Formalism.L2.SG.Pf.ProdE
  Formalism.L2.SG.Pf.ProdEP2Core Formalism.L2.SG.Pf.IndexCocycleOrbits Formalism.L2.SG.Pf.ProdEP2Cut

namespace Formalism.L2.SG.Pf.ProdEP2Uni

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem unimod_of_norm {G : Type} [Group G] (A B' : Subgroup G) (s : G) (hAB' : A ≤ B') (hB : cj s B' = B')
    (hf : A.relIndex B' ≠ 0) : IdxRatio A (cj s A) = 1 := by
  have hA'le : cj s A ≤ B' := hB ▸ cj_le hAB'
  have hA'idx : (cj s A).relIndex B' = A.relIndex B' := by rw [← relIndex_cj s A B', hB]
  have e2 := idxCocycle G A (cj s A) B' hA'le (by rw [hA'idx]; exact hf)
  have e3 := idxCocycle G A A B' hAB' hf
  rw [idxRatio_self] at e3
  rw [e2, hA'idx, ← e3]

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) {p : PlF D}

section Mat

def dg (x : (D.s.atP p).Ep) : MP p := Matrix.diagonal fun i => x ^ (i : ℕ)

theorem dg_mul_dg (x y : (D.s.atP p).Ep) : (dg x : MP p) * dg y = dg (x * y) := by
  simp only [dg, Matrix.diagonal_mul_diagonal, mul_pow]

theorem dg_one : (dg 1 : MP p) = 1 := by
  simp [dg]

theorem dg_entry (x y : (D.s.atP p).Ep) (m : MP p) (i j : Fin (D.R.rS + 1)) :
    (dg x * m * dg y) i j = x ^ (i : ℕ) * m i j * y ^ (j : ℕ) := by
  simp only [dg, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem pow_inv_pow {a : (D.s.atP p).Fp} (ha : a ≠ 0) (k : ℕ) :
    (algebraMap _ (D.s.atP p).Ep a⁻¹) ^ k * (algebraMap _ (D.s.atP p).Ep a) ^ k = 1 := by
  rw [← mul_pow, ← map_mul, inv_mul_cancel₀ ha, map_one, one_pow]

theorem pow_scale {a : (D.s.atP p).Fp} (ha : a ≠ 0) {i j : ℕ} (hij : j ≤ i) :
    (algebraMap _ (D.s.atP p).Ep a) ^ i * (algebraMap _ (D.s.atP p).Ep a⁻¹) ^ j =
      (algebraMap _ (D.s.atP p).Ep a) ^ (i - j) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [Nat.add_sub_cancel_left, pow_add, mul_comm ((algebraMap _ (D.s.atP p).Ep a) ^ j), mul_assoc,
    mul_comm ((algebraMap _ (D.s.atP p).Ep a) ^ j), pow_inv_pow ha, mul_one]

def tU (a : (D.s.atP p).Fp) (ha : a ≠ 0) : GLp p :=
  ⟨dg (algebraMap _ _ a), dg (algebraMap _ _ a⁻¹),
    by rw [dg_mul_dg, ← map_mul, mul_inv_cancel₀ ha, map_one, dg_one],
    by rw [dg_mul_dg, ← map_mul, inv_mul_cancel₀ ha, map_one, dg_one]⟩

def tG (a : (D.s.atP p).Fp) (ha : a ≠ 0) : GG p := (tU a ha, MulOpposite.op (tU a ha))

def KD (a : (D.s.atP p).Fp) (ha : a ≠ 0) : Subgroup (GG p) := cj (tG a ha) (KP M p)

theorem mem_KP {x : GG p} : x ∈ KP M p ↔
    TieN.IntLow (M p) ((x.1 : GLp p) : MP p) ∧ TieN.IntUp (M p) ((x.2.unop : GLp p) : MP p) := Iff.rfl

theorem mem_KD {a : (D.s.atP p).Fp} (ha : a ≠ 0) {x : GG p} : x ∈ KD M a ha ↔
    TieN.IntLow (M p) (dg (algebraMap _ _ a) * ((x.1 : GLp p) : MP p) * dg (algebraMap _ _ a⁻¹)) ∧
    TieN.IntUp (M p) (dg (algebraMap _ _ a⁻¹) * ((x.2.unop : GLp p) : MP p) * dg (algebraMap _ _ a)) := by
  rw [KD, mem_cj]
  show TieN.IntLow (M p) (dg (algebraMap _ _ a) * ((x.1 : GLp p) : MP p) * dg (algebraMap _ _ a⁻¹)) ∧
    TieN.IntUp (M p) (dg (algebraMap _ _ a⁻¹) * (((x.2.unop : GLp p) : MP p) * dg (algebraMap _ _ a))) ↔ _
  rw [← Matrix.mul_assoc]

end Mat

section Scale

variable {a : (D.s.atP p).Fp}

theorem intLow_scale (ha : a ≠ 0) (haO : a ∈ 𝒪[(D.s.atP p).Fp]) {l : MP p} (hl : TieN.IntLow (M p) l) :
    TieN.IntLow (M p) (dg (algebraMap _ _ a) * l * dg (algebraMap _ _ a⁻¹)) := by
  haveI := (D.s.atP p).lf
  refine ⟨fun i => ?_, fun i j hij => ?_, fun i j => ?_⟩
  · rw [dg_entry, hl.1 i, mul_one, mul_comm, pow_inv_pow ha]
  · rw [dg_entry, hl.2.1 i j hij, mul_zero, zero_mul]
  · rw [dg_entry]
    rcases le_or_gt (j : ℕ) i with h | h
    · rw [mul_right_comm, pow_scale ha h]
      exact (M p).R.mul_mem ((M p).R.pow_mem (alg_mem_R (M p) ⟨a, haO⟩) _) (hl.2.2 i j)
    · rw [hl.2.1 i j h, mul_zero, zero_mul]
      exact (M p).R.zero_mem

theorem intUp_scale (ha : a ≠ 0) (haO : a ∈ 𝒪[(D.s.atP p).Fp]) {ρ : MP p} (hρ : TieN.IntUp (M p) ρ) :
    TieN.IntUp (M p) (dg (algebraMap _ _ a⁻¹) * ρ * dg (algebraMap _ _ a)) := by
  haveI := (D.s.atP p).lf
  refine ⟨fun i => ?_, fun i j hij => ?_, fun i j => ?_⟩
  · rw [dg_entry, hρ.1 i, mul_one, pow_inv_pow ha]
  · rw [dg_entry, hρ.2.1 i j hij, mul_zero, zero_mul]
  · rw [dg_entry]
    rcases le_or_gt (i : ℕ) j with h | h
    · rw [mul_right_comm, mul_comm ((algebraMap _ (D.s.atP p).Ep a⁻¹) ^ (i : ℕ)), pow_scale ha h]
      exact (M p).R.mul_mem ((M p).R.pow_mem (alg_mem_R (M p) ⟨a, haO⟩) _) (hρ.2.2 i j)
    · rw [hρ.2.1 i j h, mul_zero, zero_mul]
      exact (M p).R.zero_mem

theorem intLow_scale_of (ha : a ≠ 0) (haO : a ∈ 𝒪[(D.s.atP p).Fp]) {l : MP p} (hl : IsLoUni l)
    (hR : ∀ i j, algebraMap _ (D.s.atP p).Ep a * l i j ∈ (M p).R) :
    TieN.IntLow (M p) (dg (algebraMap _ _ a) * l * dg (algebraMap _ _ a⁻¹)) := by
  haveI := (D.s.atP p).lf
  refine ⟨fun i => ?_, fun i j hij => ?_, fun i j => ?_⟩
  · rw [dg_entry, (hl i i).2 rfl, mul_one, mul_comm, pow_inv_pow ha]
  · rw [dg_entry, (hl i j).1 hij, mul_zero, zero_mul]
  · rw [dg_entry]
    rcases lt_trichotomy (j : ℕ) i with h | h | h
    · rw [mul_right_comm, pow_scale ha h.le]
      obtain ⟨k, hk⟩ : ∃ k, (i : ℕ) - j = k + 1 := ⟨(i : ℕ) - j - 1, by omega⟩
      rw [hk, pow_succ, mul_assoc]
      exact (M p).R.mul_mem ((M p).R.pow_mem (alg_mem_R (M p) ⟨a, haO⟩) _) (hR i j)
    · have hij : j = i := Fin.ext h
      subst hij
      rw [(hl j j).2 rfl, mul_one, mul_comm, pow_inv_pow ha]
      exact (M p).R.one_mem
    · rw [(hl i j).1 h, mul_zero, zero_mul]
      exact (M p).R.zero_mem

theorem intUp_scale_of (ha : a ≠ 0) (haO : a ∈ 𝒪[(D.s.atP p).Fp]) {ρ : MP p} (hρ : IsUpUni ρ)
    (hR : ∀ i j, algebraMap _ (D.s.atP p).Ep a * ρ i j ∈ (M p).R) :
    TieN.IntUp (M p) (dg (algebraMap _ _ a⁻¹) * ρ * dg (algebraMap _ _ a)) := by
  haveI := (D.s.atP p).lf
  refine ⟨fun i => ?_, fun i j hij => ?_, fun i j => ?_⟩
  · rw [dg_entry, (hρ i i).2 rfl, mul_one, pow_inv_pow ha]
  · rw [dg_entry, (hρ i j).1 hij, mul_zero, zero_mul]
  · rw [dg_entry]
    rcases lt_trichotomy (i : ℕ) j with h | h | h
    · rw [mul_right_comm, mul_comm ((algebraMap _ (D.s.atP p).Ep a⁻¹) ^ (i : ℕ)), pow_scale ha h.le]
      obtain ⟨k, hk⟩ : ∃ k, (j : ℕ) - i = k + 1 := ⟨(j : ℕ) - i - 1, by omega⟩
      rw [hk, pow_succ, mul_assoc]
      exact (M p).R.mul_mem ((M p).R.pow_mem (alg_mem_R (M p) ⟨a, haO⟩) _) (hR i j)
    · have hij : i = j := Fin.ext h
      subst hij
      rw [(hρ i i).2 rfl, mul_one, pow_inv_pow ha]
      exact (M p).R.one_mem
    · rw [(hρ i j).1 h, mul_zero, zero_mul]
      exact (M p).R.zero_mem

theorem intLow_of_scaled (ha : a ≠ 0) {l : MP p}
    (h : TieN.IntLow (M p) (dg (algebraMap _ _ a) * l * dg (algebraMap _ _ a⁻¹))) (hR : ∀ i j, l i j ∈ (M p).R) :
    TieN.IntLow (M p) l := by
  have hu : ∀ i j, l i j = (algebraMap _ (D.s.atP p).Ep a⁻¹) ^ (i : ℕ) *
      (dg (algebraMap _ _ a) * l * dg (algebraMap _ _ a⁻¹) : MP p) i j * (algebraMap _ (D.s.atP p).Ep a) ^ (j : ℕ) := by
    intro i j
    rw [dg_entry]
    calc l i j = ((algebraMap _ (D.s.atP p).Ep a⁻¹) ^ (i : ℕ) * (algebraMap _ (D.s.atP p).Ep a) ^ (i : ℕ)) * l i j *
          ((algebraMap _ (D.s.atP p).Ep a⁻¹) ^ (j : ℕ) * (algebraMap _ (D.s.atP p).Ep a) ^ (j : ℕ)) := by
          rw [pow_inv_pow ha, pow_inv_pow ha, one_mul, mul_one]
      _ = _ := by ring
  refine ⟨fun i => ?_, fun i j hij => ?_, hR⟩
  · rw [hu i i, h.1 i, mul_one, pow_inv_pow ha]
  · rw [hu i j, h.2.1 i j hij, mul_zero, zero_mul]

theorem intUp_of_scaled (ha : a ≠ 0) {ρ : MP p}
    (h : TieN.IntUp (M p) (dg (algebraMap _ _ a⁻¹) * ρ * dg (algebraMap _ _ a))) (hR : ∀ i j, ρ i j ∈ (M p).R) :
    TieN.IntUp (M p) ρ := by
  have hu : ∀ i j, ρ i j = (algebraMap _ (D.s.atP p).Ep a) ^ (i : ℕ) *
      (dg (algebraMap _ _ a⁻¹) * ρ * dg (algebraMap _ _ a) : MP p) i j * (algebraMap _ (D.s.atP p).Ep a⁻¹) ^ (j : ℕ) := by
    intro i j
    rw [dg_entry]
    calc ρ i j = ((algebraMap _ (D.s.atP p).Ep a⁻¹) ^ (i : ℕ) * (algebraMap _ (D.s.atP p).Ep a) ^ (i : ℕ)) * ρ i j *
          ((algebraMap _ (D.s.atP p).Ep a⁻¹) ^ (j : ℕ) * (algebraMap _ (D.s.atP p).Ep a) ^ (j : ℕ)) := by
          rw [pow_inv_pow ha, pow_inv_pow ha, one_mul, mul_one]
      _ = _ := by ring
  refine ⟨fun i => ?_, fun i j hij => ?_, hR⟩
  · rw [hu i i, h.1 i, mul_one, mul_comm, pow_inv_pow ha]
  · rw [hu i j, h.2.1 i j hij, mul_zero, zero_mul]

theorem KP_le_KD (ha : a ≠ 0) (haO : a ∈ 𝒪[(D.s.atP p).Fp]) : KP M p ≤ KD M a ha := fun x hx =>
  (mem_KD M ha).2 ⟨intLow_scale M ha haO hx.1, intUp_scale M ha haO hx.2⟩

end Scale

section Top

theorem isClosed_imp {X : Type*} [TopologicalSpace X] (P : Prop) {s : Set X} (hs : IsClosed s) :
    IsClosed {x | P → x ∈ s} := by
  by_cases h : P
  · simpa [h] using hs
  · simp [h]

include M in
theorem isClosed_loUni (p : PlF D) : IsClosed {m : MP p | IsLoUni m} := by
  haveI := (D.s.atP p).lf
  haveI := t2E (M p)
  have e : {m : MP p | IsLoUni m} = ⋂ i, ⋂ j, ({m : MP p | i < j → m ∈ {m : MP p | m i j = 0}} ∩
      {m : MP p | i = j → m ∈ {m : MP p | m i j = 1}}) := by
    ext m
    simp only [IsLoUni, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
  rw [e]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    (isClosed_imp _ (isClosed_eq (continuous_id.matrix_elem i j) continuous_const)).inter
      (isClosed_imp _ (isClosed_eq (continuous_id.matrix_elem i j) continuous_const))

include M in
theorem isClosed_upUni (p : PlF D) : IsClosed {m : MP p | IsUpUni m} := by
  haveI := (D.s.atP p).lf
  haveI := t2E (M p)
  have e : {m : MP p | IsUpUni m} = ⋂ i, ⋂ j, ({m : MP p | j < i → m ∈ {m : MP p | m i j = 0}} ∩
      {m : MP p | i = j → m ∈ {m : MP p | m i j = 1}}) := by
    ext m
    simp only [IsUpUni, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
  rw [e]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    (isClosed_imp _ (isClosed_eq (continuous_id.matrix_elem i j) continuous_const)).inter
      (isClosed_imp _ (isClosed_eq (continuous_id.matrix_elem i j) continuous_const))

theorem isClosed_intLowSet (hRcl : IsClosed ((M p).R : Set (D.s.atP p).Ep)) :
    IsClosed {l : MP p | TieN.IntLow (M p) l} := by
  haveI := (D.s.atP p).lf
  haveI := t2E (M p)
  have e : {l : MP p | TieN.IntLow (M p) l} = (⋂ i, {l : MP p | l i i = 1}) ∩
      (⋂ i, ⋂ j, {l : MP p | i < j → l ∈ {l : MP p | l i j = 0}}) ∩ ⋂ i, ⋂ j, {l : MP p | l i j ∈ (M p).R} := by
    ext l
    simp only [TieN.IntLow, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff, and_assoc]
  rw [e]
  exact ((isClosed_iInter fun i => isClosed_eq (continuous_id.matrix_elem i i) continuous_const).inter
    (isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_imp _ (isClosed_eq (continuous_id.matrix_elem i j) continuous_const))).inter
    (isClosed_iInter fun i => isClosed_iInter fun j => hRcl.preimage (continuous_id.matrix_elem i j))

theorem isClosed_intUpSet (hRcl : IsClosed ((M p).R : Set (D.s.atP p).Ep)) :
    IsClosed {l : MP p | TieN.IntUp (M p) l} := by
  haveI := (D.s.atP p).lf
  haveI := t2E (M p)
  have e : {l : MP p | TieN.IntUp (M p) l} = (⋂ i, {l : MP p | l i i = 1}) ∩
      (⋂ i, ⋂ j, {l : MP p | j < i → l ∈ {l : MP p | l i j = 0}}) ∩ ⋂ i, ⋂ j, {l : MP p | l i j ∈ (M p).R} := by
    ext l
    simp only [TieN.IntUp, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff, and_assoc]
  rw [e]
  exact ((isClosed_iInter fun i => isClosed_eq (continuous_id.matrix_elem i i) continuous_const).inter
    (isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_imp _ (isClosed_eq (continuous_id.matrix_elem i j) continuous_const))).inter
    (isClosed_iInter fun i => isClosed_iInter fun j => hRcl.preimage (continuous_id.matrix_elem i j))

theorem isCompact_intLowSet (hRc : IsCompact ((M p).R : Set (D.s.atP p).Ep)) :
    IsCompact {l : MP p | TieN.IntLow (M p) l} := by
  haveI := (D.s.atP p).lf
  haveI := t2E (M p)
  have hK : IsCompact (Set.univ.pi fun _ : Fin (D.R.rS + 1) => Set.univ.pi fun _ : Fin (D.R.rS + 1) =>
      ((M p).R : Set (D.s.atP p).Ep)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hRc
  refine hK.of_isClosed_subset (isClosed_intLowSet M hRc.isClosed) ?_
  intro l hl
  exact Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => hl.2.2 i j

theorem isCompact_intUpSet (hRc : IsCompact ((M p).R : Set (D.s.atP p).Ep)) :
    IsCompact {l : MP p | TieN.IntUp (M p) l} := by
  haveI := (D.s.atP p).lf
  haveI := t2E (M p)
  have hK : IsCompact (Set.univ.pi fun _ : Fin (D.R.rS + 1) => Set.univ.pi fun _ : Fin (D.R.rS + 1) =>
      ((M p).R : Set (D.s.atP p).Ep)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hRc
  refine hK.of_isClosed_subset (isClosed_intUpSet M hRc.isClosed) ?_
  intro l hl
  exact Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => hl.2.2 i j

theorem isCompact_KP (hRc : IsCompact ((M p).R : Set (D.s.atP p).Ep)) : IsCompact (KP M p : Set (GG p)) := by
  haveI := (D.s.atP p).lf
  haveI := topE (M p)
  haveI := t2E (M p)
  let ι : GG p → (MP p × (MP p)ᵐᵒᵖ) × (MP p × (MP p)ᵐᵒᵖ) :=
    fun x => (Units.embedProduct _ x.1, Units.embedProduct _ x.2.unop)
  have hι : Topology.IsClosedEmbedding ι :=
    Units.isClosedEmbedding_embedProduct.prodMap
      (Units.isClosedEmbedding_embedProduct.comp MulOpposite.opHomeomorph.symm.isClosedEmbedding)
  have hIL := isCompact_intLowSet M hRc
  have hIU := isCompact_intUpSet M hRc
  let Kset : Set ((MP p × (MP p)ᵐᵒᵖ) × (MP p × (MP p)ᵐᵒᵖ)) :=
    ({l : MP p | TieN.IntLow (M p) l} ×ˢ (MulOpposite.op '' {l : MP p | TieN.IntLow (M p) l})) ×ˢ
      ({l : MP p | TieN.IntUp (M p) l} ×ˢ (MulOpposite.op '' {l : MP p | TieN.IntUp (M p) l}))
  have hK : IsCompact Kset :=
    (hIL.prod (hIL.image MulOpposite.continuous_op)).prod (hIU.prod (hIU.image MulOpposite.continuous_op))
  have hcl : IsClosed (KP M p : Set (GG p)) :=
    ((isClosed_intLowSet M hRc.isClosed).preimage (Units.continuous_val.comp continuous_fst)).inter
      ((isClosed_intUpSet M hRc.isClosed).preimage
        (Units.continuous_val.comp (MulOpposite.continuous_unop.comp continuous_snd)))
  have hsub : (KP M p : Set (GG p)) ⊆ ι ⁻¹' Kset := by
    intro x hx
    have hx1 := ((mem_KP M).1 hx).1
    have hx2 := ((mem_KP M).1 hx).2
    have hy := (mem_KP M).1 ((KP M p).inv_mem hx)
    exact ⟨⟨hx1, _, hy.1, rfl⟩, hx2, _, hy.2, rfl⟩
  exact (hι.isCompact_preimage hK).of_isClosed_subset hcl hsub

theorem isCompact_KD (hRc : IsCompact ((M p).R : Set (D.s.atP p).Ep)) {a : (D.s.atP p).Fp} (ha : a ≠ 0) :
    IsCompact (KD M a ha : Set (GG p)) := by
  haveI := (D.s.atP p).lf
  haveI := topE (M p)
  rw [KD, cj, Subgroup.coe_map]
  refine (isCompact_KP M hRc).image ?_
  have e : ((MulAut.conj (tG a ha)⁻¹).toMonoidHom : GG p → GG p) =
      fun x => (tG a ha)⁻¹ * x * (tG a ha)⁻¹⁻¹ := by
    funext x
    rfl
  rw [e]
  exact (continuous_const.mul continuous_id).mul continuous_const

theorem relIndex_ne_zero (hRc : IsCompact ((M p).R : Set (D.s.atP p).Ep)) {a : (D.s.atP p).Fp} (ha : a ≠ 0)
    (S' : Subgroup (GG p)) (hS : IsClosed (S' : Set (GG p))) :
    (KP M p ⊓ S').relIndex (KD M a ha ⊓ S') ≠ 0 := by
  haveI := (D.s.atP p).lf
  haveI := topE (M p)
  haveI := t2E (M p)
  have hBc : IsCompact ((KD M a ha ⊓ S' : Subgroup (GG p)) : Set (GG p)) := (isCompact_KD M hRc ha).inter_right hS
  haveI : CompactSpace (KD M a ha ⊓ S' : Subgroup (GG p)) := isCompact_iff_compactSpace.1 hBc
  have hR : IsOpen ((M p).R : Set (D.s.atP p).Ep) := PI.ProdFormulaE.ROpen.isOpen_R (M p)
  have h1 : Continuous fun x : GG p => ((x.1 : GLp p) : MP p) := Units.continuous_val.comp continuous_fst
  have h2 : Continuous fun x : GG p => ((x.2.unop : GLp p) : MP p) :=
    Units.continuous_val.comp (MulOpposite.continuous_unop.comp continuous_snd)
  let Eset : Set (GG p) := (⋂ i, ⋂ j, (fun x : GG p => ((x.1 : GLp p) : MP p) i j) ⁻¹' ((M p).R : Set _)) ∩
    ⋂ i, ⋂ j, (fun x : GG p => ((x.2.unop : GLp p) : MP p) i j) ⁻¹' ((M p).R : Set _)
  have hE : IsOpen Eset :=
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hR.preimage (h1.matrix_elem i j)).inter
      (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hR.preimage (h2.matrix_elem i j))
  have hopen : IsOpen (((KP M p ⊓ S').subgroupOf (KD M a ha ⊓ S') : Subgroup _) :
      Set (KD M a ha ⊓ S' : Subgroup (GG p))) := by
    have e : (((KP M p ⊓ S').subgroupOf (KD M a ha ⊓ S') : Subgroup _) : Set (KD M a ha ⊓ S' : Subgroup (GG p))) =
        Subtype.val ⁻¹' Eset := by
      ext y
      obtain ⟨hK, hS'⟩ := Subgroup.mem_inf.1 y.2
      rw [mem_KD] at hK
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Set.mem_preimage, Eset,
        Set.mem_inter_iff, Set.mem_iInter, mem_KP]
      constructor
      · rintro ⟨⟨hl, hu⟩, -⟩
        exact ⟨hl.2.2, hu.2.2⟩
      · rintro ⟨hl, hu⟩
        exact ⟨⟨intLow_of_scaled M ha hK.1 hl, intUp_of_scaled M ha hK.2 hu⟩, hS'⟩
    rw [e]
    exact hE.preimage continuous_subtype_val
  have := Subgroup.quotient_finite_of_isOpen _ hopen
  show ((KP M p ⊓ S').subgroupOf (KD M a ha ⊓ S')).index ≠ 0
  exact Subgroup.index_ne_zero_of_finite

theorem idxRatio_norm (hRc : IsCompact ((M p).R : Set (D.s.atP p).Ep)) (S' : Subgroup (GG p))
    (hS : IsClosed (S' : Set (GG p))) (c : GG p) (hc1 : IsLoUni ((c.1 : GLp p) : MP p))
    (hc2 : IsUpUni ((c.2.unop : GLp p) : MP p)) (hcS : cj c S' = S') :
    IdxRatio (KP M p ⊓ S') (cj c (KP M p ⊓ S')) = 1 := by
  haveI := (D.s.atP p).lf
  obtain ⟨a, ha0, haR⟩ := common_denom (M p)
    (fun k : (Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) ⊕ (Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) =>
      Sum.elim (fun ij => ((c.1 : GLp p) : MP p) ij.1 ij.2) (fun ij => ((c.2.unop : GLp p) : MP p) ij.1 ij.2) k)
  have ha : (a : (D.s.atP p).Fp) ≠ 0 := fun h => ha0 (Subtype.ext h)
  have hcK : c ∈ KD M (a : (D.s.atP p).Fp) ha :=
    (mem_KD M ha).2 ⟨intLow_scale_of M ha a.2 hc1 fun i j => haR (Sum.inl (i, j)),
      intUp_scale_of M ha a.2 hc2 fun i j => haR (Sum.inr (i, j))⟩
  have hB : cj c (KD M (a : (D.s.atP p).Fp) ha ⊓ S') = KD M (a : (D.s.atP p).Fp) ha ⊓ S' := by
    ext g
    rw [mem_cj, Subgroup.mem_inf, Subgroup.mem_inf, ← mem_cj, ← mem_cj, cj_self hcK, hcS]
  exact unimod_of_norm _ _ c (inf_le_inf_right S' (KP_le_KD M ha a.2)) hB (relIndex_ne_zero M hRc ha S' hS)

theorem isClosed_StP (w : Point D.host.E (D.R.rS + 1)) :
    IsClosed ((StP M δ u u' w p : Subgroup (GG p)) : Set (GG p)) := by
  haveI := (D.s.atP p).lf
  haveI := topE (M p)
  haveI := t2E (M p)
  have h1 : Continuous fun x : GG p => ((x.1 : GLp p) : MP p) := Units.continuous_val.comp continuous_fst
  have h2 : Continuous fun x : GG p => ((x.2.unop : GLp p) : MP p) :=
    Units.continuous_val.comp (MulOpposite.continuous_unop.comp continuous_snd)
  exact ((isClosed_loUni M p).preimage h1).inter (((isClosed_upUni M p).preimage h2).inter
    (isClosed_eq ((h1.mul continuous_const).mul h2) continuous_const))

theorem unimodAt_holds (w : Point D.host.E (D.R.rS + 1)) : UnimodAt M δ u u' (p := p) w := by
  haveI := (D.s.atP p).lf
  haveI := (D.s.atP p).char0
  have hRc := R_compact (M p)
  intro s hs
  have hAg : Ag M δ u u' (p := p) w = KP M p ⊓ StP M δ u u' w p := by
    ext x
    rw [Ag, Subgroup.mem_map, Subgroup.mem_inf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(mem_KP M).2 hy, y.2⟩
    · rintro ⟨hK, hS⟩
      exact ⟨⟨x, hS⟩, hK, rfl⟩
  rw [hAg]
  exact idxRatio_norm M hRc _ (isClosed_StP M δ u u' w) s hs.1 hs.2.1 (cj_self hs)

variable (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))


end Top

end Formalism.L2.SG.Pf.ProdEP2Uni
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.TupGlobApprox

open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.ProdEApprox Formalism.L2.SG.Pf.PCount ValuativeRel

section Gen

theorem map3 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ} (A B C : Matrix (Fin n) (Fin n) R) :
    (A * B * C).map f = A.map f * B.map f * C.map f := by rw [Matrix.map_mul, Matrix.map_mul]

theorem split_R {Fp : Type*} [Field Fp] (O : Subring Fp) {q : Fp} (hq : q ∈ O) {x₁ x₂ d : Fp} (hd : d ∈ O)
    (h1 : x₁ - d ∈ lat O q) (h2 : x₂ - d ∈ lat O q) : x₁ ∈ O ∧ x₂ ∈ O ∧ ∃ t ∈ O, x₁ - x₂ = q * t := by
  obtain ⟨y₁, hy₁, e₁⟩ := h1
  obtain ⟨y₂, hy₂, e₂⟩ := h2
  have f₁ : x₁ = d + q * y₁ := by rw [← e₁]; ring
  have f₂ : x₂ = d + q * y₂ := by rw [← e₂]; ring
  refine ⟨?_, ?_, y₁ - y₂, O.sub_mem hy₁ hy₂, by rw [f₁, f₂]; ring⟩
  · rw [f₁]; exact O.add_mem hd (O.mul_mem hq hy₁)
  · rw [f₂]; exact O.add_mem hd (O.mul_mem hq hy₂)

end Gen

section BadG

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.TupGlob
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

theorem firstProj_mem_integers (p : PlF D) (e : (D.s.atP p).Ep ≃ₐ[(D.s.atP p).Fp] (D.s.atP p).Fp × (D.s.atP p).Fp)
    {y : (D.s.atP p).Ep} (hy : y ∈ (D.s.atP p).O) : p1 e y ∈ 𝒪[(D.s.atP p).Fp] := by
  rw [(D.s.atP p).O_def] at hy
  exact Formalism.L2.SG.Pf.LocModel.LM.DeltaC.mem_of_isIntegral_fp (D.s.atP p)
    (hy.map (((AlgHom.fst (D.s.atP p).Fp (D.s.atP p).Fp (D.s.atP p).Fp).comp e.toAlgHom).restrictScalars
      𝒪[(D.s.atP p).Fp]))

theorem p2_mem_Z2_of_mem_Z2 (p : PlF D) (e : (D.s.atP p).Ep ≃ₐ[(D.s.atP p).Fp] (D.s.atP p).Fp × (D.s.atP p).Fp)
    {y : (D.s.atP p).Ep} (hy : y ∈ (D.s.atP p).O) : p2 e y ∈ 𝒪[(D.s.atP p).Fp] := by
  rw [(D.s.atP p).O_def] at hy
  exact Formalism.L2.SG.Pf.LocModel.LM.DeltaC.mem_of_isIntegral_fp (D.s.atP p)
    (hy.map (((AlgHom.snd (D.s.atP p).Fp (D.s.atP p).Fp (D.s.atP p).Fp).comp e.toAlgHom).restrictScalars
      𝒪[(D.s.atP p).Fp]))

theorem map_stab {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ} {a Y b : Matrix (Fin n) (Fin n) R}
    (h : a * Y * b = Y) : a.map f * Y.map f * b.map f = Y.map f := by rw [← map3, h]

set_option maxHeartbeats 1000000 in
theorem target_G (u u' : D.what₂.Word) (p : PlF D) {g : Loc.SplitG (Zd.M p).L} (hM : (Zd.M p).split = some g)
    (w : Point D.host.E (D.R.rS + 1)) {Z₁ L₁ U₁ A₀ B₀ : PairVal.MatR D} (hL₁ : IsLo L₁) (hU₁ : IsUp U₁)
    (hZ : Z₁ * Sg D.host.E D.R.rS = L₁ * ptMat w * U₁) (hA₀ : IsLo A₀) (hB₀ : IsUp B₀) {l ρ : MatP D p}
    (hl : TieN.IntLow (Zd.M p) l) (hρ : TieN.IntUp (Zd.M p) ρ)
    (h : locL Zd p A₀ B₀ * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * locR Zd p A₀ B₀ =
      l * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * ρ) :
    LocTarget Zd p w L₁ U₁ A₀ B₀ := by
  have hAg := (Zd.agree p).2.2.2.2.2
  rcases hR : (D.s.atP p).split with _ | sg <;> simp only [hM, hR] at hAg
  obtain ⟨hge, hgq⟩ := hAg
  have hσ : ∀ a, fσ w (fσ w a) = a := fσ_fσ w
  have hν : ∀ a : Fin (D.R.rS + 1), pv w.1 a ≠ 0 := fun a => pv_ne' w a
  have hq0 : (sg.q : (D.s.atP p).Fp) ≠ 0 := by
    have := sg.q_irr.ne_zero
    exact_mod_cast this
  have hqO : (sg.q : (D.s.atP p).Fp) ∈ 𝒪[(D.s.atP p).Fp] := sg.q.2
  have hcv := cf_cfi Zd p
  obtain ⟨hli, -, hll'⟩ := ZsVolGrp.intLow_inv (Zd.M p) hl
  obtain ⟨hρi, -, hρρ⟩ := ZsVolGrp.intUp_inv (Zd.M p) hρ
  have hkL : IsLo (l⁻¹ * locL Zd p A₀ B₀) := isLo_mul (isLo_of_intLow Zd hli) (locL_lo Zd p hA₀ hB₀)
  have hkR : IsUp (locR Zd p A₀ B₀ * ρ⁻¹) := isUp_mul (locR_up Zd p hA₀ hB₀) (isUp_of_intUp Zd hρi)
  have hk := key_stab Zd p hl hρ h
  have hY1 : (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p).map (p1 sg.e) =
      (sg.q : (D.s.atP p).Fp)⁻¹ • (Matrix.diagonal (cf Zd p) *
        (L₁ * mono (fσ w) (fun a => pv w.1 a) * U₁).map ((p1 sg.e).comp (D.s.atP p).ιE) *
          Matrix.diagonal (cf Zd p)) -
      (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS := by
    rw [zz1' Zd p sg hR g hM hge hgq u u' Z₁, hZ, ptMat_mono']
  have hY2 : Sg (D.s.atP p).Fp D.R.rS * ((CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p).map
        (p2 sg.e)).transpose * Sg (D.s.atP p).Fp D.R.rS =
      (-(sg.q : (D.s.atP p).Fp)⁻¹) • (Matrix.diagonal (cf Zd p) *
        (L₁ * mono (fσ w) (fun a => pv w.1 a) * U₁).map ((p2 sg.e).comp (D.s.atP p).ιE) *
          Matrix.diagonal (cf Zd p)) -
      ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS := by
    rw [zz2' Zd p sg hR g hM hge hgq u u' Z₁, sign_transpose_twisted, ← sg_map ((p2 sg.e).comp (D.s.atP p).ιE), ← Matrix.map_mul, hZ,
      ptMat_mono']
  have hs1 : IsUnit ((sg.q : (D.s.atP p).Fp)⁻¹) := IsUnit.mk0 _ (inv_ne_zero hq0)
  have hs2 : IsUnit (-(sg.q : (D.s.atP p).Fp)⁻¹) := IsUnit.mk0 _ (neg_ne_zero.2 (inv_ne_zero hq0))
  have hk1 := map_stab (p1 sg.e) hk
  rw [hY1] at hk1
  have hk2 := theta_stab (map_stab (p2 sg.e) hk)
  rw [hY2] at hk2
  obtain ⟨hT1lo, hT1pat, -⟩ := comp_target ((p1 sg.e).comp (D.s.atP p).ιE) hcv hL₁ hU₁ hσ hν hs1
    (isLo_map _ hkL) (isUp_map _ hkR) hk1
  obtain ⟨hT2lo, hT2pat, -⟩ := comp_target ((p2 sg.e).comp (D.s.atP p).ιE) hcv hL₁ hU₁ hσ hν hs2
    (theta_lo (isUp_map _ hkR)) (theta_up (isLo_map _ hkL)) hk2
  obtain ⟨t, ht0, htO, hb⟩ := bnd_mats (K := (D.s.atP p).Fp) 𝒪[(D.s.atP p).Fp] (fun s hs => by simpa using hs)
    (fun x => by
      obtain ⟨s, h0, hO, hx⟩ := bounded_Fp (L := D.s.atP p) x
      exact ⟨s, h0, hO, by simpa using hx⟩)
    ![cP ((p1 sg.e).comp (D.s.atP p).ιE) (cf Zd p) L₁, cP' ((p1 sg.e).comp (D.s.atP p).ιE) (cfi Zd p) L₁,
      cQ ((p1 sg.e).comp (D.s.atP p).ιE) (cf Zd p) U₁, cQ' ((p1 sg.e).comp (D.s.atP p).ιE) (cfi Zd p) U₁,
      Matrix.of fun i _ => ((p1 sg.e).comp (D.s.atP p).ιE) (pv w.1 i),
      Matrix.of fun i _ => ((p1 sg.e).comp (D.s.atP p).ιE) (pv w.1 i)⁻¹,
      cP' ((p1 sg.e).comp (D.s.atP p).ιE) (cfi Zd p) L₁ * (l⁻¹ * locL Zd p A₀ B₀).map (p1 sg.e) *
        cP ((p1 sg.e).comp (D.s.atP p).ιE) (cf Zd p) L₁,
      cP ((p2 sg.e).comp (D.s.atP p).ιE) (cf Zd p) L₁, cP' ((p2 sg.e).comp (D.s.atP p).ιE) (cfi Zd p) L₁,
      cQ ((p2 sg.e).comp (D.s.atP p).ιE) (cf Zd p) U₁, cQ' ((p2 sg.e).comp (D.s.atP p).ιE) (cfi Zd p) U₁,
      Matrix.of fun i _ => ((p2 sg.e).comp (D.s.atP p).ιE) (pv w.1 i),
      Matrix.of fun i _ => ((p2 sg.e).comp (D.s.atP p).ιE) (pv w.1 i)⁻¹,
      cP' ((p2 sg.e).comp (D.s.atP p).ιE) (cfi Zd p) L₁ *
        (Sg (D.s.atP p).Fp D.R.rS * ((locR Zd p A₀ B₀ * ρ⁻¹).map (p2 sg.e)).transpose * Sg (D.s.atP p).Fp D.R.rS) *
        cP ((p2 sg.e).comp (D.s.atP p).ιE) (cf Zd p) L₁]
  refine ⟨glue sg.e
      (cP' ((p1 sg.e).comp (D.s.atP p).ιE) (cfi Zd p) L₁ * (l⁻¹ * locL Zd p A₀ B₀).map (p1 sg.e) *
        cP ((p1 sg.e).comp (D.s.atP p).ιE) (cf Zd p) L₁)⁻¹
      (cP' ((p2 sg.e).comp (D.s.atP p).ιE) (cfi Zd p) L₁ *
        (Sg (D.s.atP p).Fp D.R.rS * ((locR Zd p A₀ B₀ * ρ⁻¹).map (p2 sg.e)).transpose * Sg (D.s.atP p).Fp D.R.rS) *
        cP ((p2 sg.e).comp (D.s.atP p).ιE) (cf Zd p) L₁)⁻¹,
    t * (t * (t * (t * (t * (sg.q : (D.s.atP p).Fp))))), by simp [ht0, hq0], ?_⟩
  intro X' hX' hpat hfree
  obtain ⟨hgX, hgY, hst⟩ := glob_stab w hL₁ hU₁ hZ hX' hpat
  have hab := key_stab Zd p hl hρ ((corr_move Zd u u' p hA₀ hB₀ hgX hgY hst).trans h)
  have ha : IsLo (l⁻¹ * locL Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀)) :=
    isLo_mul (isLo_of_intLow Zd hli) (locL_lo Zd p (isLo_mul hA₀ hgX) (isUp_mul hgY hB₀))
  have hb' : IsUp (locR Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀) * ρ⁻¹) :=
    isUp_mul (locR_up Zd p (isLo_mul hA₀ hgX) (isUp_mul hgY hB₀)) (isUp_of_intUp Zd hρi)
  have hab1 := map_stab (p1 sg.e) hab
  rw [hY1] at hab1
  have hab2 := theta_stab (map_stab (p2 sg.e) hab)
  rw [hY2] at hab2
  have haX1 : (l⁻¹ * locL Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀)).map (p1 sg.e) =
      (l⁻¹ * locL Zd p A₀ B₀).map (p1 sg.e) * (Matrix.diagonal (cf Zd p) *
        (L₁ * X' * L₁⁻¹).map ((p1 sg.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cfi Zd p)) := by
    rw [Matrix.map_mul (L := l⁻¹) (M := locL Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀)),
      Matrix.map_mul (L := l⁻¹) (M := locL Zd p A₀ B₀), leftLocal_firstProj Zd p hM hge, leftLocal_firstProj Zd p hM hge, gX,
      Matrix.map_mul (L := A₀)]
    simp only [Matrix.mul_assoc]
    simp only [← Matrix.mul_assoc (Matrix.diagonal (cfi Zd p)) (Matrix.diagonal (cf Zd p)), diag_one (hcv'_of hcv),
      Matrix.one_mul]
  have haX2 : Sg (D.s.atP p).Fp D.R.rS * ((locR Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀) * ρ⁻¹).map
        (p2 sg.e)).transpose * Sg (D.s.atP p).Fp D.R.rS =
      (Sg (D.s.atP p).Fp D.R.rS * ((locR Zd p A₀ B₀ * ρ⁻¹).map (p2 sg.e)).transpose * Sg (D.s.atP p).Fp D.R.rS) *
        (Matrix.diagonal (cf Zd p) * (L₁ * X' * L₁⁻¹).map ((p2 sg.e).comp (D.s.atP p).ιE) *
          Matrix.diagonal (cfi Zd p)) := by
    simp only [Matrix.map_mul (L := locR Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀)),
      Matrix.map_mul (L := locR Zd p A₀ B₀), theta_mul]
    simp only [rightLocal_secondProj Zd p hM hge]
    simp only [theta_move, gX, Matrix.map_mul (L := A₀)]
    simp only [Matrix.mul_assoc]
    simp only [← Matrix.mul_assoc (Matrix.diagonal (cfi Zd p)) (Matrix.diagonal (cf Zd p)), diag_one (hcv'_of hcv),
      Matrix.one_mul]
  have hG1 : EntIn (lat 𝒪[(D.s.atP p).Fp] (t * (t * (t * (t * (t * (sg.q : (D.s.atP p).Fp)))))))
      (X'.map ((p1 sg.e).comp (D.s.atP p).ιE) -
        (cP' ((p1 sg.e).comp (D.s.atP p).ιE) (cfi Zd p) L₁ * (l⁻¹ * locL Zd p A₀ B₀).map (p1 sg.e) *
          cP ((p1 sg.e).comp (D.s.atP p).ιE) (cf Zd p) L₁)⁻¹) := by
    refine ent_free _ hσ hX' hpat hT1lo hT1pat fun i j hf => ?_
    refine Exists.elim (hfree i j hf) fun y hye => ?_
    refine ⟨p1 sg.e y, firstProj_mem_integers p sg.e hye.1, ?_⟩
    have e1 := congrArg (p1 sg.e) hye.2
    simp only [map_sub, map_mul, fst_proj_algebraMap, glue, Matrix.of_apply, fst_proj_symm] at e1
    exact e1
  have hG2 : EntIn (lat 𝒪[(D.s.atP p).Fp] (t * (t * (t * (t * (t * (sg.q : (D.s.atP p).Fp)))))))
      (X'.map ((p2 sg.e).comp (D.s.atP p).ιE) -
        (cP' ((p2 sg.e).comp (D.s.atP p).ιE) (cfi Zd p) L₁ *
          (Sg (D.s.atP p).Fp D.R.rS * ((locR Zd p A₀ B₀ * ρ⁻¹).map (p2 sg.e)).transpose *
            Sg (D.s.atP p).Fp D.R.rS) *
          cP ((p2 sg.e).comp (D.s.atP p).ιE) (cf Zd p) L₁)⁻¹) := by
    refine ent_free _ hσ hX' hpat hT2lo hT2pat fun i j hf => ?_
    refine Exists.elim (hfree i j hf) fun y hye => ?_
    refine ⟨p2 sg.e y, p2_mem_Z2_of_mem_Z2 p sg.e hye.1, ?_⟩
    have e1 := congrArg (p2 sg.e) hye.2
    simp only [map_sub, map_mul, snd_proj_algebraMap, glue, Matrix.of_apply, snd_proj_symm] at e1
    exact e1
  have hc1 := comp_main ((p1 sg.e).comp (D.s.atP p).ιE) hcv hL₁ hU₁ hσ hν hs1 (isLo_map _ hkL) (isUp_map _ hkR) hk1
    (isLo_map _ ha) (isUp_map _ hb') hab1 haX1 htO hqO
    (fun a => by simpa using hb 4 a a) (fun a => by simpa using hb 5 a a)
    (fun i j => by simpa using hb 0 i j) (fun i j => by simpa using hb 1 i j)
    (fun i j => by simpa using hb 2 i j) (fun i j => by simpa using hb 3 i j)
    (fun i j => by simpa using hb 6 i j) hG1
  have hc2 := comp_main ((p2 sg.e).comp (D.s.atP p).ιE) hcv hL₁ hU₁ hσ hν hs2 (theta_lo (isUp_map _ hkR))
    (theta_up (isLo_map _ hkL)) hk2 (theta_lo (isUp_map _ hb')) (theta_up (isLo_map _ ha)) hab2 haX2 htO hqO
    (fun a => by simpa using hb 11 a a) (fun a => by simpa using hb 12 a a)
    (fun i j => by simpa using hb 7 i j) (fun i j => by simpa using hb 8 i j)
    (fun i j => by simpa using hb 9 i j) (fun i j => by simpa using hb 10 i j)
    (fun i j => by simpa using hb 13 i j) hG2
  have hA2 : EntIn (lat 𝒪[(D.s.atP p).Fp] (sg.q : (D.s.atP p).Fp))
      ((l⁻¹ * locL Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀)).map (p2 sg.e) - 1) := by
    have := ent_theta hc2.2
    rwa [theta_sub_one, theta_theta] at this
  have hB2 : EntIn (lat 𝒪[(D.s.atP p).Fp] (sg.q : (D.s.atP p).Fp))
      ((locR Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀) * ρ⁻¹).map (p2 sg.e) - 1) := by
    have := ent_theta hc2.1
    rwa [theta_sub_one, theta_theta] at this
  have hmem : ∀ M : MatP D p, EntIn (lat 𝒪[(D.s.atP p).Fp] (sg.q : (D.s.atP p).Fp)) (M.map (p1 sg.e) - 1) →
      EntIn (lat 𝒪[(D.s.atP p).Fp] (sg.q : (D.s.atP p).Fp)) (M.map (p2 sg.e) - 1) → ∀ i j, M i j ∈ (Zd.M p).R := by
    intro M h1 h2 i j
    have hd : (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Fp) i j ∈ 𝒪[(D.s.atP p).Fp] := by
      rw [Matrix.one_apply]
      split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _
    have e1 := h1 i j
    have e2 := h2 i j
    rw [Matrix.sub_apply, Matrix.map_apply] at e1 e2
    obtain ⟨m1, m2, m3⟩ := split_R 𝒪[(D.s.atP p).Fp] hqO hd e1 e2
    refine mem_R_of (Zd.M p) g hM (M i j) (by rw [hge]; exact m1) (by rw [hge]; exact m2) ?_
    rw [hge, hgq]
    exact m3
  refine ⟨?_, ?_⟩
  · have e : locL Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀) =
        l * (l⁻¹ * locL Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀)) := by
      rw [← Matrix.mul_assoc, hll', Matrix.one_mul]
    rw [e]
    exact ZsVolGrp.intLow_mul (Zd.M p) hl ⟨ha.1, ha.2, hmem _ hc1.1 hA2⟩
  · have e : locR Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀) =
        (locR Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀) * ρ⁻¹) * ρ := by
      rw [Matrix.mul_assoc, (ZsVolGrp.intUp_inv (Zd.M p) hρ).2.1, Matrix.mul_one]
    rw [e]
    exact ZsVolGrp.intUp_mul (Zd.M p) ⟨hb'.1, fun a b hab => hb'.2 b a hab, hmem _ hc1.2 hB2⟩ hρ

end BadG

end Formalism.L2.SG.Pf.TupGlobApprox
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.TupGlobApprox

open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.ProdEApprox Formalism.L2.SG.Pf.PCount ValuativeRel

section IntM

variable {K : Type*} [CommRing K] (I : Subring K) {n : ℕ}

theorem int_mul {A B : Matrix (Fin n) (Fin n) K} (hA : ∀ i j, A i j ∈ I) (hB : ∀ i j, B i j ∈ I) :
    ∀ i j, (A * B) i j ∈ I := by
  intro i j
  rw [Matrix.mul_apply]
  exact I.sum_mem fun k _ => I.mul_mem (hA i k) (hB k j)

theorem int_diag {d : Fin n → K} (hd : ∀ a, d a ∈ I) : ∀ i j, Matrix.diagonal d i j ∈ I := by
  intro i j
  rw [Matrix.diagonal_apply]
  split_ifs
  · exact hd i
  · exact I.zero_mem

end IntM

section Good

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.TupGlob
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

theorem gY_int (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) {U₁ X' : PairVal.MatR D} (hX' : IsLo X')
    (hpat : ∀ i j, fσ w j < fσ w i → X' i j = 0) (hU : ∀ i j, (D.s.atP p).ιE (U₁ i j) ∈ (D.s.atP p).O)
    (hU' : ∀ i j, (D.s.atP p).ιE (U₁⁻¹ i j) ∈ (D.s.atP p).O)
    (hν : ∀ a : Fin (D.R.rS + 1), (D.s.atP p).ιE (pv w.1 a) ∈ (D.s.atP p).O)
    (hν' : ∀ a : Fin (D.R.rS + 1), (D.s.atP p).ιE (pv w.1 a)⁻¹ ∈ (D.s.atP p).O)
    (hX : ∀ i j, (D.s.atP p).ιE (X' i j) ∈ (D.s.atP p).O) :
    ∀ i j, ((gY w U₁ X').map (D.s.atP p).ιE) i j ∈ (D.s.atP p).O := by
  have hν0 : ∀ a : Fin (D.R.rS + 1), IsUnit (pv w.1 a) := fun a => IsUnit.mk0 _ (pv_ne' w a)
  have hup := cOf_up (fσ_fσ w) (fun a => pv w.1 a) X' hX'.1 hpat hν0
  have hc : IsUp (cOf (fσ w) (fun a => pv w.1 a) X') := ⟨hup.1, fun a b hab => hup.2 b a hab⟩
  have hcm : ∀ i j, ((cOf (fσ w) (fun a => pv w.1 a) X').map (D.s.atP p).ιE) i j ∈ (D.s.atP p).O := by
    intro i j
    simp only [Matrix.map_apply, cOf, Matrix.of_apply, Ring.inverse_eq_inv', map_mul]
    exact (D.s.atP p).O.mul_mem ((D.s.atP p).O.mul_mem (hν' _) (hX _ _)) (hν _)
  have hci : ∀ i j, (((cOf (fσ w) (fun a => pv w.1 a) X')⁻¹).map (D.s.atP p).ιE) i j ∈ (D.s.atP p).O := by
    intro i j
    rw [ZsVolGrp.inv_eq_adj (det_up' hc)]
    have e := RingHom.map_adjugate (D.s.atP p).ιE (cOf (fσ w) (fun a => pv w.1 a) X')
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at e
    rw [e]
    exact ZsVolGrp.adj_mem (D.s.atP p).O hcm i j
  simp only [gY, Matrix.map_mul]
  exact int_mul _ (int_mul _ hU' hci) hU

theorem good_at (p : PlF D) (hM : (Zd.M p).split = none) (w : Point D.host.E (D.R.rS + 1))
    {L₁ U₁ A₀ B₀ X' : PairVal.MatR D} (hL₁ : IsLo L₁) (hU₁ : IsUp U₁) (hA₀ : IsLo A₀) (hB₀ : IsUp B₀)
    (hX' : IsLo X') (hpat : ∀ i j, fσ w j < fσ w i → X' i j = 0)
    (hcf : ∀ a, algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a) ∈ (D.s.atP p).O)
    (hcfi : ∀ a, algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a) ∈ (D.s.atP p).O)
    (hA : ∀ i j, (D.s.atP p).ιE (A₀ i j) ∈ (D.s.atP p).O) (hB : ∀ i j, (D.s.atP p).ιE (B₀ i j) ∈ (D.s.atP p).O)
    (hL : ∀ i j, (D.s.atP p).ιE (L₁ i j) ∈ (D.s.atP p).O) (hL' : ∀ i j, (D.s.atP p).ιE (L₁⁻¹ i j) ∈ (D.s.atP p).O)
    (hU : ∀ i j, (D.s.atP p).ιE (U₁ i j) ∈ (D.s.atP p).O) (hU' : ∀ i j, (D.s.atP p).ιE (U₁⁻¹ i j) ∈ (D.s.atP p).O)
    (hν : ∀ a : Fin (D.R.rS + 1), (D.s.atP p).ιE (pv w.1 a) ∈ (D.s.atP p).O)
    (hν' : ∀ a : Fin (D.R.rS + 1), (D.s.atP p).ιE (pv w.1 a)⁻¹ ∈ (D.s.atP p).O)
    (hX : ∀ i j, (D.s.atP p).ιE (X' i j) ∈ (D.s.atP p).O) : GoodAt Zd p w L₁ U₁ A₀ B₀ X' := by
  obtain ⟨hgX, hgY, -⟩ : IsLo (gX L₁ X') ∧ IsUp (gY w U₁ X') ∧ True := by
    have hν0 : ∀ a : Fin (D.R.rS + 1), IsUnit (pv w.1 a) := fun a => IsUnit.mk0 _ (pv_ne' w a)
    have hup := cOf_up (fσ_fσ w) (fun a => pv w.1 a) X' hX'.1 hpat hν0
    have hc : IsUp (cOf (fσ w) (fun a => pv w.1 a) X') := ⟨hup.1, fun a b hab => hup.2 b a hab⟩
    exact ⟨isLo_mul (isLo_mul hL₁ hX') (isLo_inv hL₁), isUp_mul (isUp_mul (isUp_inv hU₁) (isUp_inv hc)) hU₁, trivial⟩
  have hgYi := gY_int p w hX' hpat hU hU' hν hν' hX
  have hR : (Zd.M p).R = (D.s.atP p).O := Formalism.L2.SG.Pf.LMK.R_eq_O (Zd.agree p) hM
  have hlo := locL_lo Zd p (isLo_mul hA₀ hgX) (isUp_mul hgY hB₀)
  have hup := locR_up Zd p (isLo_mul hA₀ hgX) (isUp_mul hgY hB₀)
  refine ⟨⟨hlo.1, hlo.2, fun i j => ?_⟩, ⟨hup.1, fun a b hab => hup.2 b a hab, fun i j => ?_⟩⟩
  · rw [hR, locL_L Zd p hM]
    refine int_mul _ (int_mul _ (int_diag _ hcf) ?_) (int_diag _ hcfi) i j
    simp only [gX, Matrix.map_mul]
    exact int_mul _ hA (int_mul _ (int_mul _ hL hX) hL')
  · rw [hR, locR_L Zd p hM]
    refine int_mul _ (int_mul _ (int_diag _ hcfi) ?_) (int_diag _ hcf) i j
    rw [Matrix.map_mul]
    exact int_mul _ hgYi hB

end Good

end Formalism.L2.SG.Pf.TupGlobApprox
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.TupGlobApprox

open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.ProdEApprox Formalism.L2.SG.Pf.PCount ValuativeRel
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.TupGlob
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem locTarget (Zd : LocDat D) (u u' : D.what₂.Word) (p : PlF D) (w : Point D.host.E (D.R.rS + 1))
    {Z₁ L₁ U₁ A₀ B₀ : PairVal.MatR D} (hL₁ : IsLo L₁) (hU₁ : IsUp U₁)
    (hZ : Z₁ * Sg D.host.E D.R.rS = L₁ * ptMat w * U₁) (hA₀ : IsLo A₀) (hB₀ : IsUp B₀) {l ρ : MatP D p}
    (hl : TieN.IntLow (Zd.M p) l) (hρ : TieN.IntUp (Zd.M p) ρ)
    (h : locL Zd p A₀ B₀ * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * locR Zd p A₀ B₀ =
      l * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * ρ) :
    LocTarget Zd p w L₁ U₁ A₀ B₀ := by
  rcases hM : (Zd.M p).split with _ | g
  · exact target_L Zd u u' p hM w hL₁ hU₁ hZ hA₀ hB₀ hl hρ h
  · exact target_G Zd u u' p hM w hL₁ hU₁ hZ hA₀ hB₀ hl hρ h

theorem cf_int (Zd : LocDat D) (p : PlF D) (hδ1 : Zd.δ p ∈ 𝒪[(D.s.atP p).Fp])
    (hδ2 : (Zd.δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp]) (hu1 : (D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O)
    (hu2 : (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) ∈ (D.s.atP p).O) :
    (∀ a, algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a) ∈ (D.s.atP p).O) ∧
      ∀ a, algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a) ∈ (D.s.atP p).O := by
  have e1 : (D.s.atP p).ιE ((uP p : ℚ) : D.host.E) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF ((uP p : ℚ) : D.host.F)) := by
    rw [← (D.s.atP p).compat, map_ratCast (algebraMap D.host.F D.host.E)]
  have e2 : (D.s.atP p).ιE (((uP p : ℚ) : D.host.E)⁻¹) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (((D.s.atP p).ιF ((uP p : ℚ) : D.host.F))⁻¹) := by
    rw [← map_inv₀ (D.s.atP p).ιF, ← (D.s.atP p).compat, map_inv₀ (algebraMap D.host.F D.host.E),
      map_ratCast (algebraMap D.host.F D.host.E)]
  have hy : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (yP Zd p) ∈ (D.s.atP p).O := by
    unfold yP
    rw [map_mul, ← e1]
    exact (D.s.atP p).O.mul_mem (LocModel.LM.algebraMap_mem_O p hδ1) hu1
  have hyi : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (yP Zd p)⁻¹ ∈ (D.s.atP p).O := by
    unfold yP
    rw [mul_inv, map_mul, ← e2]
    exact (D.s.atP p).O.mul_mem (LocModel.LM.algebraMap_mem_O p hδ2) hu2
  exact ⟨fun a => by unfold cf; rw [map_pow]; exact pow_mem hyi _,
    fun a => by unfold cfi; rw [map_pow]; exact pow_mem hy _⟩

theorem stabApprox (Zd : LocDat D) (u u' : D.what₂.Word) : Formalism.L2.SG.Pf.TupGlob.StabApprox Zd u u' := by
  intro w Z₁ A₀ B₀ hAt hA₀ hB₀ hloc
  obtain ⟨L₁, U₁, hL₁u, hU₁u, e₁⟩ := hAt
  have hL₁ : IsLo L₁ := isLo_of_uni hL₁u
  have hU₁ : IsUp U₁ := isUp_of_uni hU₁u
  rw [zhatOM_eq] at e₁
  choose l ρ hl hρ hlr using hloc
  choose T c hc0 hT using fun p => locTarget Zd u u' p w hL₁ hU₁ e₁ hA₀ hB₀ (hl p) (hρ p) (hlr p)
  have hE : ∀ᶠ p in Filter.cofinite, ∀ (k : Fin 8) (i j : Fin (D.R.rS + 1)),
      (D.s.atP p).ιE ((![A₀, B₀, L₁, L₁⁻¹, U₁, U₁⁻¹, Matrix.of fun i _ => pv w.1 i,
        Matrix.of fun i _ => (pv w.1 i)⁻¹] : Fin 8 → PairVal.MatR D) k i j) ∈ (D.s.atP p).O :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      LocModel.LM.iotaIntegral_almost_all D _
  have hG := (LocModel.good_cofinite Zd.δ Zd.M Zd.agree ∅).and hE
  have hfin := Filter.eventually_cofinite.1 hG
  choose t ht1 ht2 using fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) =>
    sa_lat D.s.atP hfin.toFinset (fun p => T p ij.1 ij.2) c (fun p _ => hc0 p)
  let X' : PairVal.MatR D := Matrix.of fun i j => if Free (fσ w) i j then t (i, j) else (1 : PairVal.MatR D) i j
  have hX'1 : ∀ i j, ¬ Free (fσ w) i j → X' i j = (1 : PairVal.MatR D) i j := fun i j h => by
    simp only [X', Matrix.of_apply, if_neg h]
  have hX'2 : ∀ i j, Free (fσ w) i j → X' i j = t (i, j) := fun i j h => by
    simp only [X', Matrix.of_apply, if_pos h]
  have hX' : IsLo X' :=
    ⟨fun a => by rw [hX'1 a a (fun h => lt_irrefl a h.1), Matrix.one_apply_eq],
      fun a b hab => by rw [hX'1 a b (fun h => absurd h.1 (not_lt.2 hab.le)), Matrix.one_apply_ne hab.ne]⟩
  have hpat : ∀ i j, fσ w j < fσ w i → X' i j = 0 := fun i j hij => by
    have hf : ¬ Free (fσ w) i j := fun h => absurd h.2 (not_lt.2 hij.le)
    have hne : i ≠ j := fun e => by rw [e] at hij; exact lt_irrefl _ hij
    rw [hX'1 i j hf, Matrix.one_apply_ne hne]
  obtain ⟨hgX, hgY, hst⟩ := glob_stab w hL₁ hU₁ e₁ hX' hpat
  refine ⟨gX L₁ X', gY w U₁ X', hgX, hgY, hst, fun p => ?_⟩
  by_cases hp : p ∈ hfin.toFinset
  · exact hT p X' hX' hpat fun i j hf => by rw [hX'2 i j hf]; exact ht1 (i, j) p hp
  · have hgp : _ ∧ _ := not_not.1 ((Set.Finite.mem_toFinset hfin).not.1 hp)
    obtain ⟨⟨hM, ⟨hδ1, hδ2⟩, ⟨hu1, hu2⟩, -⟩, hEp⟩ := hgp
    obtain ⟨hcf, hcfi⟩ := cf_int Zd p hδ1 hδ2 hu1 hu2
    have hXi : ∀ i j, (D.s.atP p).ιE (X' i j) ∈ (D.s.atP p).O := by
      intro i j
      by_cases hf : Free (fσ w) i j
      · rw [hX'2 i j hf]; exact ht2 (i, j) p hp
      · rw [hX'1 i j hf, Matrix.one_apply]
        split_ifs
        · rw [map_one]; exact Subring.one_mem _
        · rw [map_zero]; exact Subring.zero_mem _
    exact good_at Zd p hM w hL₁ hU₁ hA₀ hB₀ hX' hpat hcf hcfi
      (fun i j => hEp 0 i j) (fun i j => hEp 1 i j) (fun i j => hEp 2 i j) (fun i j => hEp 3 i j)
      (fun i j => hEp 4 i j) (fun i j => hEp 5 i j) (fun a => hEp 6 a a) (fun a => hEp 7 a a) hXi

end Formalism.L2.SG.Pf.TupGlobApprox
end
end

section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cutLeavesDeep_of_betaInt (D : Formalism.BasicNotions.D7)
    (hB : ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
      (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
      (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)), BetaInt ⟨δ, M, hA⟩ u u' F0 what₂) :
    Formalism.L2.SG.Pf.Coef.CutLeavesDeep D := by
  intro _ δ M hA _ u u' hc hP F0 what₂ hR
  refine ⟨fun γ w F' L U hE p => ⟨Formalism.L2.SG.Pf.CountAt.countAt_holds (M := M) (δ := δ) (γ := γ) (w := w) (F' := F') (L := L) (U := U) (hE := hE) (p := p) ..,
    by intros; apply Formalism.L2.SG.Pf.ProdEP2Uni.unimodAt_holds⟩,
    Formalism.L2.SG.Pf.TupGlobApprox.stabApprox _ u u', ?_⟩
  exact fStarC_of_int ⟨δ, M, hA⟩ ⟨hc, hR, hP⟩ (hB δ M hA u u' F0 what₂)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end
