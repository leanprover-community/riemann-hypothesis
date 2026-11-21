import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.AdmissibleTraceRegular
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.NormalOfCenter
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.GlobNegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FinMulSupp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.JstdTrace
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.ResidualAutomorphyOfLinkedEnds
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.EmbAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.CommOfConj

section
open NumberField UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Glob.gqS :
    UpperTheory.V.Z.Sym.Glob.GqS := by
  intro F _ _ Δ D hD ι hι t ht τ hτ γ j hγ hj
  haveI := hD.real
  have hreg : τ ^ 2 - 4 ≠ 0 := cm_ne hτ
  have htr : ∀ (g : DX Δ) (v : Pl F), HasTr g τ → HasTr ((ι g).1 v) (cv v τ) :=
    fun g v hg => hasTr_map (cv v) (hι g v) hg
  by_cases hA : D.admitted t τ
  · rw [show one (D.admitted t τ) = 1 from if_pos hA, one_mul]
    refine gqD D hD ι hι t ht τ hτ hA γ j hγ hj γ (D.fSv t) ?_ (fun v => ((D.S v).cS : ℂ))
      (fun v => gOrb (Ov v) (jstd ((cv v) τ)) 1 (toUnit QuadraticAlgebra.omega)) ?_
    · intro v u hu x
      by_cases hv : v ∈ D.Sg
      · have hS := hD.sig v hv
        have hu' : u ∈ (D.S v).J2 := by simpa [Dat.J2v, hv] using hu
        simp only [Dat.fSv, if_pos hv]
        rw [(hS.S_inv (t v) (ht v hv) u hu' _).2, (hS.S_inv (t v) (ht v hv) u⁻¹ (inv_mem hu') _).1]
      · have hu' : u ∈ KD ((cv v) Δ) (Ov v) := by simpa [Dat.J2v, hv] using hu
        have hiff : u⁻¹ * x * u ∈ KD ((cv v) Δ) (Ov v) ↔ x ∈ KD ((cv v) Δ) (Ov v) := by
          rw [(KD ((cv v) Δ) (Ov v)).mul_mem_cancel_right hu',
            (KD ((cv v) Δ) (Ov v)).mul_mem_cancel_left (inv_mem hu')]
        simp only [Dat.fSv, if_neg hv, one]
        by_cases hx : x ∈ KD ((cv v) Δ) (Ov v)
        · rw [if_pos hx, if_pos (hiff.2 hx)]
        · rw [if_neg hx, if_neg (fun h => hx (hiff.1 h))]
    · intro v jv hjv
      have hgv : HasTr ((ι γ).1 v) (cv v τ) := htr γ v hγ
      have hrv := cv_reg hreg v
      obtain ⟨z, hz⟩ := zEx hrv
      refine ⟨emb_comm hjv, ?_⟩
      by_cases hv : v ∈ D.Sg
      · have hS := hD.sig v hv
        obtain ⟨hF, -, hO, -, -⟩ := hS.D_orb (t v) (ht v hv) _ _ jv hrv hgv hjv z hz
        have e1 : D.fSv t v = (D.S v).fS (t v) := by
          funext g
          simp [Dat.fSv, hv]
        have e2 : D.J2v v = (D.S v).J2 := by simp [Dat.J2v, hv]
        rw [e1, e2]
        refine ⟨hF, fun _ => ?_, fun h => absurd hv h⟩
        rw [hO, show one (Ind _ _ _) = 1 from if_pos (hA v hv), mul_one]
      · have hL := hD.off v hv
        have e1 : D.fSv t v = fun g => one (g ∈ KD ((cv v) Δ) (Ov v)) := by
          funext g
          simp [Dat.fSv, hv]
        have e2 : D.J2v v = KD ((cv v) Δ) (Ov v) := by simp [Dat.J2v, hv]
        rw [e1, e2]
        refine ⟨(finD _ _ _ _ hL hrv _ jv hgv hjv).1, fun h => absurd h hv, fun _ =>
          ⟨(locD _ _ _ _ hL hrv _ jv hgv hjv (D.χ v) (hD.chi v).1 z hz).1, fun hK hu =>
            ⟨if_pos hK, fun y hy => ?_⟩⟩⟩
        have hy' : y⁻¹ * (ι γ).1 v * y ∈ ZD ((cv v) Δ) ⊔ KD ((cv v) Δ) (Ov v) := by
          by_contra hn
          exact hy (if_neg (fun h => hn (le_sup_right (a := ZD ((cv v) Δ)) h)))
        exact (oneD _ _ _ _ hL hrv _ jv hgv hjv hK hu).2.1 y hy'
  · rw [show one (D.admitted t τ) = 0 from if_neg hA, zero_mul, mul_zero]
    apply gqOn_zero
    intro y
    obtain ⟨v, hv, hI⟩ : ∃ v ∈ D.Sg, ¬ Ind (D.S v).H ((cv v) τ) (t v) := by
      simpa [Dat.admitted] using hA
    have heq : ((Quotient.out y)⁻¹ * ι γ * Quotient.out y).1 v =
        ((Quotient.out y).1 v)⁻¹ * (ι γ).1 v * (Quotient.out y).1 v := rfl
    have hgtr : HasTr (((Quotient.out y)⁻¹ * ι γ * Quotient.out y).1 v) (cv v τ) := by
      rw [heq]
      exact hasTr_conj (htr γ v hγ) _
    have hz : D.fSv t v (((Quotient.out y)⁻¹ * ι γ * Quotient.out y).1 v) = 0 := by
      simp only [Dat.fSv, if_pos hv]
      by_contra hne
      exact hI ((hD.sig v hv).S_supp (t v) (ht v hv) _ _ hgtr hne)
    exact fin_mulSupp (D.fSv t) D.Sg (fun w hw k hk => by simp [Dat.fSv, hw, one, hk]) _ hz
end

section
namespace UpperTheory.V.Z.Sym.Glob

open NumberField Loc

private theorem aux_statement_10 {F : Type} [Field F] [NumberField F] {Δ : F} (D : Dat Δ) (hD : D.Ok) (t : Dat.Par F)
    (ht : D.Cone t) (τ : F) (h : D.admitted t τ) : τ ^ 2 - 4 ≠ 0 := by
  intro h0
  obtain ⟨v, hv⟩ := hD.ne
  refine ((hD.sig v hv).reg (t v) (ht v hv) _ (h v hv)).2 ?_
  have h2 : IsIntegral (Ov v) (2 : Kv v) := by
    have := isIntegral_algebraMap (R := Ov v) (A := Kv v) (x := 2)
    rwa [map_ofNat] at this
  have h1 : (τ - 2) * (τ + 2) = 0 := by rw [← h0]; ring
  rcases mul_eq_zero.mp h1 with h1 | h1
  · rw [sub_eq_zero.mp h1, map_ofNat]; exact h2
  · rw [eq_neg_of_add_eq_zero_left h1, map_neg, map_ofNat]; exact h2.neg

private theorem sum_sub {α : Type} (p : α → Prop) (f : α → ℂ) (c : ℂ) :
    ∑ᶠ i : {a // p a}, c * f i.1 = c * ∑ᶠ a, one (p a) * f a := by
  classical
  have h1 : ∑ᶠ i : {a // p a}, c * f i.1 = ∑ᶠ (a) (_ : p a), c * f a :=
    finsum_subtype_eq_finsum_cond (f := fun a => c * f a) p
  rw [h1]
  have h2 : ∀ a, ∑ᶠ (_ : p a), c * f a = c • (one (p a) * f a) := by
    intro a
    rw [finsum_eq_if, smul_eq_mul]
    unfold one
    split_ifs <;> simp
  simp_rw [h2]
  rw [← smul_finsum, smul_eq_mul]

set_option maxHeartbeats 1600000 in
theorem split_side_identity_unitary : QuaternionStableSideTraceIdentity := by
  intro F _ _ Δ D hD x₀ hx₀
  obtain ⟨-, ⟨ι, hι⟩, -⟩ := iotaEx F Δ
  obtain ⟨n, x, c, hx0, hoff, hc, hsum⟩ := fibre F Δ D hD ι hι x₀ hx₀
  have hΔ : Δ ≠ 0 := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
    obtain ⟨σ⟩ : Nonempty (F →+* ℝ) := ⟨InfinitePlace.embedding_of_isReal (hD.real.isReal w)⟩
    have hneg : σ Δ < 0 := hD.neg σ
    intro h0
    rw [h0, map_zero] at hneg
    exact lt_irrefl _ hneg
  refine ⟨n, x, c * ∏ v ∈ D.Sg, (D.S v).cS, hx0, hoff, ?_, ?_⟩
  · exact mul_pos hc (Finset.prod_pos fun v hv => (hD.sig v hv).cS)
  · intro V _ _ _ ch B hB t ht
    classical
    have hG : ∀ a, D.Good t a ↔ IsCM a ∧ D.admitted t a := fun a => Iff.rfl
    have hex : ∀ s : {a // D.Good t a}, ∃ g : DX Δ, HasTr g s.1 :=
      fun s => (embEx F Δ D hD s.1).1 ((hG _).1 s.2).1
    choose γ hγ using hex
    have hreg : ∀ s : {a // D.Good t a}, s.1 ^ 2 - 4 ≠ 0 :=
      fun s => aux_statement_10 D hD t ht s.1 ((hG _).1 s.2).2
    have hj : ∀ s : {a // D.Good t a}, ∃ j : (Etau F s.1)ˣ →* DX Δ, IsEmb s.1 (γ s) j :=
      fun s => (embAlg F Δ s.1 hΔ (hreg s) (γ s) (hγ s)).1
    choose j hjj using hj
    rw [hsum V ch B hB t ht {a // D.Good t a} (fun s => s.1) γ j Subtype.val_injective
      (fun s => ⟨hreg s, hγ s, hjj s⟩) ?_]
    · have hterm : ∀ s : {a // D.Good t a},
          ch s.1 * gqOn (ι.comp (j s)) (scalE s.1) D.UZ
            (fun y => D.FS t ((Quotient.out y)⁻¹ * ι (γ s) * Quotient.out y)) =
            (∏ v ∈ D.Sg, ((D.S v).cS : ℂ)) * (ch s.1 * ms s.1 * D.nS s.1) := by
        intro s
        rw [gqS F Δ D hD ι hι t ht s.1 ((hG _).1 s.2).1 (γ s) (j s) (hγ s) (hjj s)]
        have h1 : one (D.admitted t s.1) = 1 := if_pos ((hG _).1 s.2).2
        rw [h1]
        ring
      rw [finsum_congr hterm, sum_sub (fun a => D.Good t a) (fun a => ch a * ms a * D.nS a)]
      unfold Dat.sumS
      push_cast
      ring
    · intro g s hg hs
      exact ⟨⟨s, (hG s).2 ⟨(embEx F Δ D hD s).2 g hg (aux_statement_10 D hD t ht s hs), hs⟩⟩, rfl⟩

end UpperTheory.V.Z.Sym.Glob
end

section
open NumberField UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

private theorem tau_eq {K : Type} [Field K] {Δ τ τ' : K} (hr : τ ^ 2 - 4 ≠ 0) {γ : DX Δ} {j} (hγ : HasTr γ τ) (hj : IsEmb τ γ j)
    {z : (Etau K τ)ˣ} (hz : (z : Etau K τ) = 1 + QuadraticAlgebra.omega) (y : DX Δ)
    (h : (mt (y⁻¹ * j z * y)).trace ^ 2 = algebraMap K _ (2 + τ') * (mt (y⁻¹ * j z * y)).det) : τ' = τ := by
  have e : mt (y⁻¹ * j z * y) = mt y⁻¹ * mt (j z) * mt y := rfl
  have e' : mt y * mt y⁻¹ = 1 := by
    change mt (y * y⁻¹) = 1
    rw [mul_inv_cancel]; rfl
  have e1 : mt (j z) = 1 + mt γ := by rw [hj, hz]; simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  have h1 := hγ.1
  have h2 := hγ.2
  rw [Matrix.det_fin_two] at h1
  rw [Matrix.trace_fin_two] at h2
  have t1 : (mt (j z)).trace = algebraMap K _ (2 + τ) := by
    rw [e1, Matrix.trace_fin_two, map_add, map_ofNat, ← h2]; simp; ring
  have t2 : (mt (j z)).det = algebraMap K _ (2 + τ) := by
    rw [e1, Matrix.det_fin_two, map_add, map_ofNat, ← h2]; simp; linear_combination h1
  rw [e, Matrix.trace_mul_cycle, e', one_mul, Matrix.det_mul, mul_comm _ (mt y).det, Matrix.det_mul, ← mul_assoc (mt y).det,
    ← Matrix.det_mul, e', Matrix.det_one, one_mul, t1, t2, ← map_pow, ← map_mul] at h
  have h3 := (algebraMap K (Lsq K Δ)).injective h
  have h4 : 2 + τ ≠ 0 := fun e => hr (by linear_combination (τ - 2) * e)
  exact mul_right_cancel₀ h4 (by linear_combination -h3)

theorem UpperTheory.V.Z.Sym.Glob.gqK :
    UpperTheory.V.Z.Sym.Glob.GqK := by
  classical
  intro F _ _ Δ D hD ι hι t ht τ hτ γ j hγ hj z hz
  haveI := hD.real
  have hr := cm_ne hτ
  have htr : ∀ v, HasTr ((ι γ).1 v) (cv v τ) := fun v => hasTr_map _ (hι γ v) hγ
  have f1 : ∀ v ∈ D.Sg, D.fKv t v = (D.S v).fK (t v) := fun v hv => funext fun g => if_pos hv
  have f2 : ∀ v ∉ D.Sg, D.fKv t v = fZD (Ov v) (D.χ v) := fun v hv => funext fun g => if_neg hv
  have J1 : ∀ v ∈ D.Sg, D.J2v v = (D.S v).J2 := fun v hv => if_pos hv
  have J2 : ∀ v ∉ D.Sg, D.J2v v = KD _ (Ov v) := fun v hv => if_neg hv
  choose zv hzv using fun v => zEx (cv_reg hr v)
  have ez : ∀ v jv, IsEmb (cv v τ) ((ι γ).1 v) jv → (ι (j z)).1 v = jv (zv v) := fun v jv hjv =>
    dx_ext ((hι (j z) v).trans (emb_map _ (hι γ v) hj hjv z _ (by
      rw [hzv, hz]; ext <;> simp [emap, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one])).symm)
  have k1 : ∀ v ∉ D.Sg, ∀ k ∈ KD _ (Ov v), fZD (Ov v) (D.χ v) k = 1 := fun v hv k hk => by
    have := (Loc.fzdLaw _ _ _ (hD.off v hv) _ (hD.chi v).1).2 1 1 k (by simp [IsScal, mt]) hk
    simpa using this
  by_cases hA : D.admitted t τ
  · rw [show one (D.admitted t τ) = 1 from if_pos hA, one_mul]
    refine gqD D hD ι hι t ht τ hτ hA γ j hγ hj (j z) (D.fKv t) (fun v => ?_) _ _ fun v jv hjv => ?_
    · by_cases hv : v ∈ D.Sg
      · rw [f1 v hv, J1 v hv]
        intro u hu x
        rw [(((hD.sig v hv).K_inv _ (ht v hv)).1 u hu _).2, (((hD.sig v hv).K_inv _ (ht v hv)).1 _ (inv_mem hu) _).1]
      · rw [f2 v hv, J2 v hv]
        exact fZD_conj _ (hD.off v hv) _ (hD.chi v).1
    · rw [ez v jv hjv]
      refine ⟨fun s => by rw [← map_mul, ← map_mul, mul_comm], ?_⟩
      by_cases hv : v ∈ D.Sg
      · rw [f1 v hv, J1 v hv]
        obtain ⟨-, h1, -, h3, -⟩ := (hD.sig v hv).D_orb _ (ht v hv) _ _ _ (cv_reg hr v) (htr v) hjv _ (hzv v)
        exact ⟨h1, fun _ => by rw [h3, show one (Ind _ _ _) = 1 from if_pos (hA v hv), mul_one], fun h => absurd hv h⟩
      · rw [f2 v hv, J2 v hv]
        refine ⟨(Loc.finD _ _ _ _ (hD.off v hv) (cv_reg hr v) _ _ (htr v) hjv).2.1 _ (hzv v) _, fun h => absurd h hv, fun _ =>
          ⟨(locD _ _ _ _ (hD.off v hv) (cv_reg hr v) _ _ (htr v) hjv _ (hD.chi v).1 _ (hzv v)).2, fun h1 h2 => ?_⟩⟩
        obtain ⟨h3, h4⟩ := (Loc.oneD _ _ _ _ (hD.off v hv) (cv_reg hr v) _ _ (htr v) hjv h1 h2).2.2 _ (hzv v)
        refine ⟨k1 v hv _ h3, fun y hy => h4 y ?_⟩
        by_contra h
        exact hy ((Loc.fzdLaw _ _ _ (hD.off v hv) _ (hD.chi v).1).1 _ h)
  · rw [show one (D.admitted t τ) = 0 from if_neg hA, zero_mul, mul_zero]
    refine gqOn_zero _ _ _ _ fun y => ?_
    obtain ⟨v, hv⟩ := not_forall.1 hA
    obtain ⟨hv, hI⟩ := Classical.not_imp.1 hv
    refine fin_mulSupp (D.fKv t) D.Sg (fun v hv k hk => by rw [f2 v hv]; exact k1 v hv k hk) _ (v := v) ?_
    rw [f1 v hv]
    by_contra h
    haveI : CharZero (Kv v) := algebraRat.charZero _
    obtain ⟨jv, hjv⟩ := (embAlg (Kv v) _ _ ((map_ne_zero _).2 hD.ne0) (cv_reg hr v) _ (htr v)).1
    have h' : (D.S v).fK (t v) ((y.out.1 v)⁻¹ * (ι (j z)).1 v * y.out.1 v) ≠ 0 := h
    rw [ez v jv hjv] at h'
    obtain ⟨τ', h1, h2⟩ := (hD.sig v hv).K_supp _ (ht v hv) _ h'
    exact hI (tau_eq (cv_reg hr v) (htr v) hjv (hzv v) _ h2 ▸ h1)
end

section
noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open NumberField IsDedekindDomain Matrix Loc MulAction

private theorem quot_sum_congr {Y : Type} (s s' : Setoid Y) (h : s = s') (k k' : Y → ℂ) (hk : k = k') :
    (∑ᶠ o : Quotient s, k o.out) = ∑ᶠ o : Quotient s', k' o.out := by
  subst h; subst hk; rfl

private theorem gqOn_surj {H' H G : Type} [Group H'] [Group H] [Group G] (e : H' →* H) (he : Function.Surjective e)
    (j : H →* G) (H₀ : Subgroup H) (U : Subgroup G) (k : G ⧸ U → ℂ) :
    gqOn (j.comp e) (H₀.comap e) U k = gqOn j H₀ U k := by
  letI a : MulAction H (G ⧸ U) := MulAction.compHom _ j
  letI a' : MulAction H' (G ⧸ U) := MulAction.compHom _ (j.comp e)
  have hs : ∀ (x : H') (y : G ⧸ U), x • y = e x • y := fun _ _ => rfl
  refine quot_sum_congr (orbitRel H' (G ⧸ U)) (orbitRel H (G ⧸ U)) ?_
    (fun y => k y / ((H₀.comap e).relIndex (stabilizer H' y) : ℂ)) (fun y => k y / (H₀.relIndex (stabilizer H y) : ℂ)) ?_
  · ext x y
    rw [orbitRel_apply, orbitRel_apply, mem_orbit_iff, mem_orbit_iff]
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨e g, hg⟩
    · rintro ⟨g, hg⟩
      obtain ⟨g', rfl⟩ := he g
      exact ⟨g', hg⟩
  · funext y
    have : stabilizer H' y = (stabilizer H y).comap e := by
      ext x; simp only [mem_stabilizer_iff, Subgroup.mem_comap, hs]
    rw [this, Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective he]

section Field

variable {K : Type} [Field K] {Δ : K}

private theorem mem_DX_k (g : GL (Fin 2) (Lsq K Δ)) : g ∈ DX Δ ↔
    ((g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 1 1 = star ((g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 0 0) ∧
    (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 1 0 = - star ((g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 0 1)) := by
  have e : g ∈ DX Δ ↔ (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).map (starRingEnd _) =
      !![0, -1; 1, 0] * (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * !![0, 1; -1, 0] := by
    unfold DX
    exact Units.ext_iff
  rw [e]
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, starRingEnd_apply] at h00 h01
    exact ⟨h00.symm, by rw [h01, neg_neg]⟩
  · rintro ⟨h1, h2⟩
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [starRingEnd_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, h1, h2]

private theorem tr_det_rat (g : DX Δ) : ∃ a b : K, (mt g).trace = algebraMap K _ a ∧ (mt g).det = algebraMap K _ b ∧ b ≠ 0 := by
  obtain ⟨h1, h2⟩ : mt g 1 1 = star (mt g 0 0) ∧ mt g 1 0 = - star (mt g 0 1) := (mem_DX_k _).1 g.2
  have hd : (mt g).det = algebraMap K _ (QuadraticAlgebra.norm (mt g 0 0) + QuadraticAlgebra.norm (mt g 0 1)) := by
    rw [Matrix.det_fin_two, h1, h2, map_add, QuadraticAlgebra.algebraMap_norm_eq_mul_star, QuadraticAlgebra.algebraMap_norm_eq_mul_star]
    ring
  refine ⟨2 * (mt g 0 0).re, _, ?_, hd, ?_⟩
  · rw [Matrix.trace_fin_two, h1]
    ext <;> simp [two_mul]
  · intro h
    rw [h, map_zero] at hd
    exact (Matrix.isUnits_det_units (g : GL (Fin 2) (Lsq K Δ))).ne_zero hd

private theorem mt_mul (a b : DX Δ) : mt (a * b) = mt a * mt b := rfl

private theorem mt_inj {a b : DX Δ} (h : mt a = mt b) : a = b := Subtype.ext (Units.ext h)

private theorem tr_conj (x g : DX Δ) : (mt (x⁻¹ * g * x)).trace = (mt g).trace := by
  rw [mt_mul, Matrix.trace_mul_comm, ← mt_mul, ← mul_assoc, mul_inv_cancel, one_mul]

private theorem det_conj (x g : DX Δ) : (mt (x⁻¹ * g * x)).det = (mt g).det := by
  rw [mt_mul, Matrix.det_mul_comm, ← mt_mul, ← mul_assoc, mul_inv_cancel, one_mul]

private theorem mem_ZD (z : DX Δ) : z ∈ ZD Δ ↔ ∃ s : Kˣ, mt z = algebraMap K (Lsq K Δ) s • 1 := by
  unfold ZD
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range]
  refine exists_congr fun s => ?_
  rw [← Units.val_inj, eq_comm]
  have : ((((GeneralLinearGroup.scalar (Fin 2)).comp (Units.map (algebraMap K (Lsq K Δ) : K →* Lsq K Δ))) s : GL (Fin 2) (Lsq K Δ)) :
      Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = algebraMap K (Lsq K Δ) s • 1 := by
    ext i j : 1
    simp [Matrix.diagonal_apply, Matrix.one_apply]
  rw [this]

private theorem alg_inj : Function.Injective (algebraMap K (Lsq K Δ)) := (algebraMap K (Lsq K Δ)).injective

private theorem one_add {τ : K} {γ : DX Δ} {j : (Etau K τ)ˣ →* DX Δ} (hj : IsEmb τ γ j) {z : (Etau K τ)ˣ}
    (hz : (z : Etau K τ) = 1 + QuadraticAlgebra.omega) : mt (j z) = 1 + mt γ := by
  rw [hj z, hz]
  simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

private theorem det_one_add (M : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) : (1 + M).det = 1 + M.trace + M.det := by
  simp only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.add_apply, Matrix.one_apply]
  simp
  ring

private theorem tr_det_one_add {τ : K} {γ δ : DX Δ} (hγ : HasTr γ τ) (h : mt δ = 1 + mt γ) :
    (mt δ).trace = algebraMap K _ (2 + τ) ∧ (mt δ).det = algebraMap K _ (2 + τ) := by
  rw [h, det_one_add, Matrix.trace_add, hγ.1, hγ.2, Matrix.trace_one, map_add, map_ofNat]
  refine ⟨by simp, by ring⟩

private theorem rel_inj {a b : K} (hb : b ≠ 0) {δ δ' x z : DX Δ} (hz : z ∈ ZD Δ)
    (h1 : (mt δ).trace = algebraMap K _ a) (h2 : (mt δ).det = algebraMap K _ a)
    (h1' : (mt δ').trace = algebraMap K _ b) (h2' : (mt δ').det = algebraMap K _ b)
    (h : δ' = x⁻¹ * δ * x * z) : a = b ∧ z = 1 := by
  obtain ⟨s, hs⟩ := (mem_ZD z).1 hz
  have e : mt δ' = algebraMap K (Lsq K Δ) s • mt (x⁻¹ * δ * x) := by
    rw [h, mt_mul, hs, Matrix.mul_smul, Matrix.mul_one]
  rw [e, Matrix.trace_smul, tr_conj, h1, smul_eq_mul, ← map_mul] at h1'
  rw [e, Matrix.det_smul, det_conj, h2, Fintype.card_fin, ← map_pow, ← map_mul] at h2'
  have e1 := alg_inj h1'
  have e2 := alg_inj h2'
  have hs1 : (s : K) = 1 := by
    apply mul_right_cancel₀ hb
    rw [one_mul]
    calc (s : K) * b = s * (s * a) := by rw [e1]
      _ = b := by rw [← e2]; ring
  refine ⟨by rw [← e1, hs1, one_mul], mt_inj ?_⟩
  rw [hs, hs1, map_one, one_smul]
  rfl

private theorem scal_ex (s : Kˣ) : ∃ z ∈ ZD Δ, mt z = algebraMap K (Lsq K Δ) s • 1 := by
  have hd : IsUnit (algebraMap K (Lsq K Δ) s • (1 : Matrix (Fin 2) (Fin 2) (Lsq K Δ))) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_smul, Matrix.det_one, mul_one]
    exact (s.isUnit.map _).pow _
  have hm : hd.unit ∈ DX Δ := by
    rw [mem_DX_k, IsUnit.unit_spec]
    constructor
    · ext <;> simp
    · simp
  exact ⟨⟨hd.unit, hm⟩, (mem_ZD _).2 ⟨s, rfl⟩, rfl⟩

private theorem cover {τ a b : K} {g : DX Δ} (h1 : (mt g).trace = algebraMap K _ a) (h2 : (mt g).det = algebraMap K _ b)
    (hb : b ≠ 0) (hτ : 2 + τ ≠ 0) (h : a ^ 2 = (2 + τ) * b) :
    ∃ γ : DX Δ, HasTr γ τ ∧ ∃ z ∈ ZD Δ, mt g = (1 + mt γ) * mt z := by
  have ha : a ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hτ hb (by rw [← h]; ring)
  have hs : a / (2 + τ) ≠ 0 := div_ne_zero ha hτ
  obtain ⟨z, hz, hz'⟩ := scal_ex (Δ := Δ) (Units.mk0 _ hs)
  set r : K := (2 + τ) / a with hr
  have hra : r * a = 2 + τ := by rw [hr]; field_simp
  have hrb : r ^ 2 * b = 2 + τ := by
    rw [hr, div_pow, h]; field_simp
  set M : Matrix (Fin 2) (Fin 2) (Lsq K Δ) := algebraMap K (Lsq K Δ) r • mt g - 1 with hM
  have hM1 : 1 + M = algebraMap K (Lsq K Δ) r • mt g := by rw [hM]; abel
  have htr : M.trace = algebraMap K _ τ := by
    rw [hM, Matrix.trace_sub, Matrix.trace_smul, h1, smul_eq_mul, ← map_mul, hra, Matrix.trace_one, map_add, map_ofNat]
    simp
  have hdet : M.det = 1 := by
    have := det_one_add M
    rw [hM1, Matrix.det_smul, h2, Fintype.card_fin, ← map_pow, ← map_mul, hrb, htr, map_add, map_ofNat] at this
    linear_combination -this
  have hd : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, hdet]
    exact isUnit_one
  obtain ⟨k1, k2⟩ : mt g 1 1 = star (mt g 0 0) ∧ mt g 1 0 = - star (mt g 0 1) := (mem_DX_k _).1 g.2
  have hst : star (algebraMap K (Lsq K Δ) r) = algebraMap K (Lsq K Δ) r := by ext <;> simp
  have hm : hd.unit ∈ DX Δ := by
    rw [mem_DX_k, IsUnit.unit_spec, hM]
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, k1, k2, star_sub, star_mul', hst]
    simp
  refine ⟨⟨hd.unit, hm⟩, ⟨hdet, htr⟩, z, hz, ?_⟩
  change mt g = (1 + M) * mt z
  rw [hM1, hz', Matrix.mul_smul, Matrix.mul_one, smul_smul, ← map_mul, Units.val_mk0]
  have : a / (2 + τ) * r = 1 := by rw [hr]; field_simp
  rw [this, map_one, one_smul]

private theorem unit_ex {τ : K} (hτ : 2 + τ ≠ 0) : ∃ z : (Etau K τ)ˣ, (z : Etau K τ) = 1 + QuadraticAlgebra.omega := by
  have : (1 + QuadraticAlgebra.omega : Etau K τ) * ⟨(1 + τ) / (2 + τ), -1 / (2 + τ)⟩ = 1 := by
    ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> field_simp <;> ring
  exact ⟨Units.mkOfMulEqOne _ _ this, rfl⟩

private theorem two_add_ne {τ : K} (h : τ ^ 2 - 4 ≠ 0) : 2 + τ ≠ 0 := fun e => h (by linear_combination (τ - 2) * e)

private theorem reg_of_not_int {O : Type} [CommRing O] [Algebra O K] {τ : K} (h : ¬ IsIntegral O τ) : τ ^ 2 - 4 ≠ 0 := by
  intro e
  have h2 : IsIntegral O (2 : K) := by
    have := (isIntegral_one (R := O) (B := K)).add (isIntegral_one (R := O) (B := K))
    rwa [one_add_one_eq_two] at this
  have : (τ - 2) * (τ + 2) = 0 := by linear_combination e
  rcases mul_eq_zero.1 this with e | e
  · exact h (by rw [sub_eq_zero.1 e]; exact h2)
  · exact h (by rw [eq_neg_of_add_eq_zero_left e]; exact h2.neg)

private theorem lmap_alg {K' : Type} [Field K'] (f : K →+* K') (a : K) :
    lmap f Δ (algebraMap K (Lsq K Δ) a) = algebraMap K' (Lsq K' (f Δ)) (f a) := by
  ext <;> simp [lmap]

private theorem local_tau {K' : Type} [Field K'] (f : K →+* K') {g : DX Δ} {g' y : DX (f Δ)} (hg : mt g' = (mt g).map (lmap f Δ))
    {a b : K} (h1 : (mt g).trace = algebraMap K _ a) (h2 : (mt g).det = algebraMap K _ b) (hb : b ≠ 0) {τ : K'}
    (h : (mt (y⁻¹ * g' * y)).trace ^ 2 = algebraMap K' _ (2 + τ) * (mt (y⁻¹ * g' * y)).det) : f (a ^ 2 / b - 2) = τ := by
  have e1 : (mt g').trace = algebraMap K' _ (f a) := by
    rw [hg, ← lmap_alg, ← h1]
    simp [Matrix.trace_fin_two]
  have e2 : (mt g').det = algebraMap K' _ (f b) := by
    rw [hg, ← lmap_alg, ← h2]
    simp [Matrix.det_fin_two]
  rw [tr_conj, det_conj, e1, e2, ← map_pow, ← map_mul] at h
  have e := alg_inj h
  have hb' : f b ≠ 0 := (map_ne_zero f).2 hb
  rw [map_sub, map_div₀, map_pow, map_ofNat, e]
  field_simp
  ring

private theorem term_eq [CharZero K] {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (B : Base (DX Δ) G V) (hΓ : B.Γ₀ = ZD Δ)
    (hΔ : Δ ≠ 0) {τ : K} (hτ : τ ^ 2 - 4 ≠ 0) {γ : DX Δ} (hγ : HasTr γ τ) {j : (Etau K τ)ˣ →* DX Δ} (hj : IsEmb τ γ j)
    {z : (Etau K τ)ˣ} (hz : (z : Etau K τ) = 1 + QuadraticAlgebra.omega) (f : G → ℂ) :
    (Base.Tw.one B).term f (j z) = LinearMap.trace ℂ V (B.W (j z)) *
      gqOn (B.ι.comp j) (scalE τ) B.U (fun y => f (y.out⁻¹ * B.ι (j z) * y.out)) := by
  obtain ⟨-, h2, h3⟩ := (embAlg K Δ τ hΔ hτ γ hγ).2.1 j hj
  have hδ := one_add hj hz
  obtain ⟨t1, t2⟩ := tr_det_one_add hγ hδ
  have hc : ∀ x, x ∈ (Base.Tw.one B).Cent (j z) ↔ x ∈ j.range := fun x => by
    constructor
    · rintro ⟨w, hw, e⟩
      change x⁻¹ * j z * x = j z * w at e
      rw [hΓ] at hw
      have e' : j z = x⁻¹ * j z * x * w⁻¹ := by rw [e, mul_inv_cancel_right]
      have hw1 := (rel_inj (two_add_ne hτ) (inv_mem hw) t1 t2 t1 t2 e').2
      rw [hw1, mul_one, mul_assoc, eq_inv_mul_iff_mul_eq] at e'
      have e2 := congrArg mt e'
      rw [mt_mul, mt_mul, hδ, mul_add, add_mul, mul_one, one_mul, add_right_inj] at e2
      exact (h2 x).2 (mt_inj e2)
    · rintro ⟨w, rfl⟩
      refine ⟨1, one_mem _, ?_⟩
      change (j w)⁻¹ * j z * j w = j z * 1
      rw [← map_inv, ← map_mul, ← map_mul, mul_one, mul_right_comm, inv_mul_cancel, one_mul]
  let e : (Etau K τ)ˣ →* (Base.Tw.one B).Cent (j z) := j.codRestrict _ fun w => (hc _).2 ⟨w, rfl⟩
  have he : Function.Surjective e := fun x => by
    obtain ⟨w, hw⟩ := (hc x).1 x.2
    exact ⟨w, Subtype.ext hw⟩
  have key := gqOn_surj e he (B.ι.comp ((Base.Tw.one B).Cent (j z)).subtype) (B.Γ₀.subgroupOf _) B.U ((Base.Tw.one B).ker f (j z))
  have k2 : (B.Γ₀.subgroupOf ((Base.Tw.one B).Cent (j z))).comap e = scalE τ := by
    rw [← h3, hΓ]
    rfl
  rw [k2] at key
  unfold Base.Tw.term
  rw [← key]
  rfl

end Field

section Global

variable {F : Type} [Field F] [NumberField F] {Δ : F} {D : Dat Δ}

private theorem supp (hD : D.Ok) (t : Dat.Par F) (g : DA Δ) (h : D.FK t g ≠ 0) (v : Pl F) (hv : v ∈ D.Sg) :
    (D.S v).fK (t v) (g.1 v) ≠ 0 := by
  classical
  have hfin : (Function.mulSupport fun v => D.fKv t v (g.1 v)).Finite := by
    refine (D.Sg.finite_toSet.union (Filter.eventually_cofinite.1 ((rpg _ _).ae g))).subset fun w hw => ?_
    by_contra hn
    rw [Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at hn
    apply hw
    have := (fzdLaw (Ov w) (Kv w) (cv w Δ) (hD.off w hn.1) (D.χ w) (hD.chi w).1).2 1 1 (g.1 w) (by simp [IsScal]) hn.2
    have hw' : w ∉ D.Sg := hn.1
    rw [one_mul] at this
    simp only [Dat.fKv, if_neg hw', this, map_one, inv_one, Units.val_one]
  intro h0
  apply h
  unfold Dat.FK
  refine finprod_eq_zero _ v ?_ hfin
  simp only [Dat.fKv, if_pos hv, h0]

private theorem real_emb (hD : D.Ok) : Nonempty (F →+* ℝ) := by
  have := hD.real
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact ⟨InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)⟩

private theorem cover_glob (hD : D.Ok) {ι : DX Δ →* DA Δ} (hι : IsIotaD ι) {t : Dat.Par F} (ht : D.Cone t) (g : DX Δ) (y : DA Δ)
    (h : D.FK t (y⁻¹ * ι g * y) ≠ 0) :
    ∃ τ, D.Good t τ ∧ ∃ γ : DX Δ, HasTr γ τ ∧ ∃ z ∈ ZD Δ, mt g = (1 + mt γ) * mt z := by
  obtain ⟨a, b, h1, h2, hb⟩ := tr_det_rat g
  have hadm : ∀ v ∈ D.Sg, Ind (D.S v).H (cv v (a ^ 2 / b - 2)) (t v) := fun v hv => by
    obtain ⟨τ, hτ, e⟩ := (hD.sig v hv).K_supp (t v) (ht v hv) _ (supp hD t _ h v hv)
    have e' : (y⁻¹ * ι g * y).1 v = (y.1 v)⁻¹ * (ι g).1 v * y.1 v := rfl
    rw [e'] at e
    rw [local_tau (cv v) (hι g v) h1 h2 hb e]
    exact hτ
  have hreg : (a ^ 2 / b - 2) ^ 2 - 4 ≠ 0 := by
    obtain ⟨v, hv⟩ := hD.ne
    have := reg_of_not_int ((hD.sig v hv).reg (t v) (ht v hv) _ (hadm v hv)).2
    intro e
    apply this
    have e2 := congrArg (cv v) e
    rwa [map_sub, map_pow, map_ofNat, map_zero] at e2
  obtain ⟨γ, hγ, r⟩ := cover h1 h2 hb (two_add_ne hreg) (by field_simp; ring)
  exact ⟨_, ⟨(embEx F Δ D hD _).2 γ hγ hreg, hadm⟩, γ, hγ, r⟩

end Global

end UpperTheory.V.Z.Sym.Glob

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob in
theorem UpperTheory.V.Z.Sym.Glob.sideK :
    UpperTheory.V.Z.Sym.Glob.SideK := by
  classical
  intro F _ _ Δ D hD
  refine ⟨∏ v ∈ D.Sg, (D.S v).cK, Finset.prod_pos fun v hv => (hD.sig v hv).cK, ?_⟩
  intro V _ _ _ ch B hB t ht
  obtain ⟨σ⟩ := real_emb hD
  have hΔ : Δ ≠ 0 := fun e => by
    have := hD.neg σ
    rw [e, map_zero] at this
    exact lt_irrefl _ this
  have hreg : ∀ i : {τ // D.Good t τ}, i.1 ^ 2 - 4 ≠ 0 := fun i e => by
    have := i.2.1 σ
    rw [e, map_zero] at this
    exact lt_irrefl _ this
  choose γ hγ using fun i : {τ // D.Good t τ} => (embEx F Δ D hD i.1).1 i.2.1
  choose j hj using fun i : {τ // D.Good t τ} => (embAlg F Δ i.1 hΔ (hreg i) (γ i) (hγ i)).1
  choose z hz using fun i : {τ // D.Good t τ} => unit_ex (two_add_ne (hreg i))
  have hδ := fun i => one_add (hj i) (hz i)
  have htd := fun i => tr_det_one_add (hγ i) (hδ i)
  obtain ⟨hfin, htest⟩ := finK F Δ D hD V ch B hB
  have hι : IsIotaD B.ι := hB.ι
  have key := (Tf.trace _ _ V B hfin (Base.Tw.one B) (D.FK t) (htest t ht) {τ // D.Good t τ} (fun i => j i (z i)) ?_ ?_).2
  · rw [key]
    have e : ∀ i : {τ // D.Good t τ}, (Base.Tw.one B).term (D.FK t) (j i (z i)) =
        ((∏ v ∈ D.Sg, (D.S v).cK : ℝ) : ℂ) * (ch i.1 * ms i.1 * D.nK i.1) := fun i => by
      rw [term_eq B hB.Γ₀ hΔ (hreg i) (hγ i) (hj i) (hz i), hB.tr _ _ (htd i).1 (htd i).2, hB.U,
        gqK F Δ D hD B.ι hι t ht i.1 i.2.1 (γ i) (j i) (hγ i) (hj i) (z i) (hz i)]
      have : one (D.admitted t i.1) = 1 := if_pos i.2.2
      rw [this]
      push_cast
      ring
    rw [finsum_congr e, ← mul_finsum, Dat.sumK,
      finsum_subtype_eq_finsum_cond (f := fun τ => ch τ * ms τ * D.nK τ) (p := D.Good t)]
    congr 1
    refine finsum_congr fun τ => ?_
    rw [finsum_eq_if, one]
    split_ifs <;> simp
  · rintro i i' ⟨x, w, hw, e⟩
    rw [hB.Γ₀] at hw
    have := (rel_inj (two_add_ne (hreg i')) hw (htd i).1 (htd i).2 (htd i').1 (htd i').2 e).1
    exact Subtype.ext (add_left_cancel this)
  · rintro g ⟨y, hy⟩
    obtain ⟨τ, hτ, γ', hγ', w, hw, e⟩ := cover_glob hD hι ht g y.out hy
    obtain ⟨x, hx⟩ := (embAlg F Δ τ hΔ (hreg ⟨τ, hτ⟩) (γ ⟨τ, hτ⟩) (hγ ⟨τ, hτ⟩)).2.2 γ' hγ'
    refine ⟨⟨τ, hτ⟩, x, w, hB.Γ₀ ▸ hw, mt_inj ?_⟩
    change mt g = mt (x⁻¹ * j ⟨τ, hτ⟩ (z ⟨τ, hτ⟩) * x * w)
    have hx1 : mt x⁻¹ * mt x = 1 := by rw [← mt_mul, inv_mul_cancel]; rfl
    rw [e, hx, mt_mul, mt_mul, mt_mul, mt_mul, mt_mul, hδ, mul_add (mt x⁻¹), add_mul _ _ (mt x), mul_one, hx1]
end
end

section
open UpperTheory.V.Z.Sym.Glob

private theorem alg {g e c k : ℝ} (hc : 0 < c) (hk : 0 < k) {A B C S K : ℂ} (h1 : A = g * (S + e * K)) (h2 : B = c * S) (h3 : C = k * K) :
    A = ((g / c : ℝ) : ℂ) * B + ((g * e / k : ℝ) : ℂ) * C := by
  subst h1 h2 h3
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  push_cast
  field_simp

set_option maxHeartbeats 1000000 in
theorem UpperTheory.V.Z.Sym.Glob.tFId0 : TFId0 := by
  unfold TFId0
  intro F iF iN Δ D hD x₀ hx
  obtain ⟨cG, hG⟩ := @sideG F iF iN Δ D hD
  obtain ⟨e, hG⟩ := hG
  obtain ⟨cK, hK⟩ := @sideK F iF iN Δ D hD
  obtain ⟨n, hS⟩ := @split_side_identity_unitary F iF iN Δ D hD x₀ hx
  obtain ⟨x, hS⟩ := hS
  obtain ⟨cS, hS⟩ := hS
  refine ⟨n, x, cG / cS, cG * e / cK, hS.1, hS.2.1, div_pos hG.1 hS.2.2.1, ?_⟩
  intro VG VS VK a1 a2 a3 a4 a5 a6 a7 a8 a9 ch BG s BS BK hBG hBS hBK t ht
  exact alg hS.2.2.1 hK.1 (@hG.2 VG a1 a2 a3 ch BG s hBG t ht) (@hS.2.2.2 VS a4 a5 a6 ch BS hBS t ht) (@hK.2 VK a7 a8 a9 ch BK hBK t ht)
end
