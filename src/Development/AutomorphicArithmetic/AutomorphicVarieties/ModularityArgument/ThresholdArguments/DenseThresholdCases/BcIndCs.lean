import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.WsIIOfPrintsH
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PotentialModularityTower
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Hypotheses4Z
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.SeedII
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InducedFinalStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MixSeedOf
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.FinalH
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.PrOrd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.PlainAtRTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutNewform2A
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SVROrdIrr
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfPropMV
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.RatioWOfHasSat
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExRS
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfHRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocCompR
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.BaseChangeNorms.PropMHol
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.FinOfKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.ContRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.LevelP
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.IndAutLOfAutCsP
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SplitUnramifiedInduction.PolMix
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BirthAwChain
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BirthSphOfUnrW
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EGIndAutCs

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
open scoped Matrix
namespace UpperTheory.V.Sd.S2
section Alg
variable {k : Type} [Field k]
variable {Γ₀ Γ : Type} [Group Γ₀] [Group Γ]
end Alg
section Norm
variable {l : ℕ} [Fact l.Prime]
end Norm
section Gal
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
variable {D : Raw Ω c} (T : Tower D)
end Gal
def Final_s : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D)
    (ι : Qbar l ≃+* ℂ) (P : PD T.ι (G T.F Ω) (Qbar l)), GlobOk T P.r → LocOk T P → T.IsSeedAlt ι P →
    ∃ (c₁ : Coef l) (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O), T.SeedPairAlt ι h Q ∧
      Fr.InV (Φ := T.fr ∅) (Q.map (residue c₁.O)) ∧
      (Ent (Q.map (residue c₁.O)).r (-wAl) ∨ (Ent (Q.map (residue c₁.O)).r wBe ∧ Ent (Q.map (residue c₁.O)).r (-wTh)))
end UpperTheory.V.Sd.S2
end
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.ConjugateSelfDual IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Sd.S2
section
variable {R R' : Type} [CommRing R] [CommRing R'] (j : R →+* R')
private theorem fin_adj (X : M4 R) : adj (X.map j) = (adj X).map j := by
  ext a b
  simp only [adj_apply, Matrix.map_apply, map_zsmul]
private theorem fin_conj (X Y : M4 R) : adj (X.map j) * Y.map j * X.map j = (adj X * Y * X).map j := by
  rw [fin_adj, Matrix.map_mul, Matrix.map_mul]
private theorem fin_gsp (hj : Function.Injective j) (ν : R) (X : M4 R) (h : IsGSp (j ν) (X.map j)) : IsGSp ν X := by
  unfold IsGSp at h ⊢
  rw [fin_adj, ← Matrix.map_mul] at h
  ext a b
  apply hj
  have h1 := congrFun (congrFun h a) b
  rw [Matrix.map_apply] at h1
  rw [h1]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_mul]
  split_ifs <;> simp
private theorem fin_psi {ι Γ : Type} [Group Γ] (P : PD ι Γ R) (v : ι) (i : Fin 4) (s : Γ) :
    (P.map j).ψ v i s = j (P.ψ v i s) :=
  congrFun (congrFun (fin_conj j (P.n v) (P.r s)) i) i
end
private theorem fin_q (i j : Fin 4) (h : i ≠ j) (h' : wt i j ∉ qQ) : i < j ∨ (i = 2 ∧ j = 1) := by
  revert i j; decide
private theorem fin_v (w : ℤ × ℤ) (h : w ∉ nP) : w ∉ vV := by
  simp only [nP, vV, Finset.mem_insert, Finset.mem_singleton] at h ⊢
  tauto
theorem UpperTheory.induced_final_statement_alt :
    _root_.UpperTheory.V.Sd.S2.Final_s := by
  intro Ω _ _ _ l _ c D T ι P hG hL hS
  haveI : IsGalois T.F Ω := IsAlgClosure.isGalois T.F Ω
  obtain ⟨c₁, h, Q, hQ, hc⟩ := (UpperTheory.automorphic_forms_descent_to_smaller_level l c).2 T.ι (G T.F Ω) P hG.cont hG.int fun v => (hL.low v).2.1
  subst hQ
  have hinj : Function.Injective (algebraMap c₁.O (Qbar l)) := Subtype.val_injective
  have hz : ∀ x : c₁.O, residue c₁.O x = 0 ↔ ‖algebraMap c₁.O (Qbar l) x‖ < 1 := fun x =>
    (residue_eq_zero_iff x).trans ((UpperTheory.automorphic_forms_descent_to_smaller_level l c₁).1 x).2
  have hne : ∀ x : c₁.O, ‖algebraMap c₁.O (Qbar l) x‖ = 1 → residue c₁.O x ≠ 0 := fun x hx h0 =>
    absurd ((hz x).1 h0) (by rw [hx]; exact lt_irrefl _)
  have heq : ∀ x y : c₁.O, ‖algebraMap c₁.O (Qbar l) x - algebraMap c₁.O (Qbar l) y‖ < 1 →
      residue c₁.O x = residue c₁.O y := fun x y hxy => by
    rw [← sub_eq_zero, ← map_sub, hz, map_sub]
    exact hxy
  have h0 : ∀ x : c₁.O, algebraMap c₁.O (Qbar l) x = 0 → x = 0 := fun x hx => hinj (by rw [hx, map_zero])
  have hV : Supp vV (Q.map (residue c₁.O)).r := fun g i j hij hw => (hz _).2 (hG.supp g i j hij hw)
  have hq : ∀ v, SuppM qQ ((Q.map (residue c₁.O)).n v) := fun v i j hij hw => by
    rcases fin_q i j hij hw with hlt | ⟨rfl, rfl⟩
    · refine (hz _).2 ?_
      have h1 : algebraMap c₁.O (Qbar l) (Q.n v i j) = 0 := (hL.low v).1.2.2 i j hlt
      rw [h1, norm_zero]
      exact one_pos
    · exact (hz _).2 (hL.low v).2.2.1
  refine ⟨c₁, h, Q, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hc, ⟨?_, ?_, Or.inl ⟨?_, hq⟩⟩, hS⟩,
    ⟨hV, fun v => ⟨hq v, hne _ (hL.low v).2.2.2⟩⟩, ?_⟩
  · exact fun g => fin_gsp _ hinj _ _ (hG.mult g)
  · intro g hg
    ext i j
    have h1 := congrFun (congrFun (hG.kill g hg) i) j
    have h2 : algebraMap c₁.O (Qbar l) ((1 : M4 c₁.O) i j) = (1 : M4 (Qbar l)) i j := by
      simp only [Matrix.one_apply]
      split_ifs <;> simp
    exact h1.trans h2.symm
  · exact fun i j hij => h0 _ (hG.nrm hij)
  · intro v
    obtain ⟨a1, a2, a3⟩ := (hL.low v).1
    refine ⟨fin_gsp _ hinj _ _ (by rw [map_one]; exact a1), fun i => hinj (by rw [map_one]; exact a2 i),
      fun i j hij => h0 _ (a3 i j hij)⟩
  · intro v s hs i j hij
    refine h0 _ ?_
    have h1 := hL.flag v s hs i j hij
    exact (congrFun (congrFun (fin_conj (algebraMap c₁.O (Qbar l)) (Q.n v) (Q.r s)) i) j).symm.trans h1
  · intro v s hs i
    refine hinj ?_
    exact ((fin_psi (algebraMap c₁.O (Qbar l)) Q v i s).symm.trans (hL.mu v s hs i)).trans (map_one _).symm
  · exact fun g i => heq _ _ (hG.diag g i)
  · intro v s hs i
    refine (fin_psi (residue c₁.O) Q v i s).trans (heq _ _ ?_)
    have h1 := hL.char v s hs i
    rw [fin_psi (algebraMap c₁.O (Qbar l)) Q v i s] at h1
    exact h1
  · exact fun g i j hij hw => hV g i j hij (fin_v _ hw)
  · rcases hG.ent with ⟨g, hg⟩ | ⟨⟨g, hg⟩, g', hg'⟩
    · exact Or.inl ⟨g, 1, 0, by decide, hne _ hg⟩
    · exact Or.inr ⟨⟨g, 1, 2, by decide, hne _ hg⟩, g', 3, 0, by decide, hne _ hg'⟩
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V UpperTheory.V.Z.Win.Birth
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2
section
variable {l : ℕ} [Fact l.Prime]
private theorem lt_add {a b : Qbar l} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a + b‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans_lt (max_lt ha hb)
private theorem norm_of_cong {a b : Qbar l} (h : ‖a - b‖ < 1) (hb : ‖b‖ = 1) : ‖a‖ = 1 := by
  have e : a = (a - b) + b := by ring
  rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hb]; exact h.ne), hb, max_eq_right h.le]
private theorem root_ex {a : Qbar l} (ha : ‖a - 1‖ < 1) {z : (Qbar l)ˣ} (hz : Cong z 1 ∨ Cong z (-1)) :
    ∃ α : (Qbar l)ˣ, (α : Qbar l) ^ 2 = a ∧ Cong α z := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq a two_pos
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [← hx] at ha
    simp at ha
  have h1 : ∃ y : Qbar l, y ≠ 0 ∧ y ^ 2 = a ∧ ‖y - 1‖ < 1 := by
    have e : ‖x - 1‖ * ‖-x - 1‖ < 1 := by
      rw [← norm_mul, show (x - 1) * (-x - 1) = -(a - 1) by rw [← hx]; ring, norm_neg]
      exact ha
    by_cases h : ‖x - 1‖ < 1
    · exact ⟨x, hx0, hx, h⟩
    · refine ⟨-x, neg_ne_zero.2 hx0, by rw [← hx]; ring, ?_⟩
      nlinarith [norm_nonneg (-x - 1), not_lt.1 h]
  obtain ⟨y, hy0, hy, hy1⟩ := h1
  rcases hz with hz | hz
  · refine ⟨Units.mk0 y hy0, hy, ?_⟩
    have := lt_add hy1 (by rw [norm_neg]; exact hz : ‖-((z : Qbar l) - ((1 : (Qbar l)ˣ) : Qbar l))‖ < 1)
    simpa [Cong] using this
  · refine ⟨-Units.mk0 y hy0, by simpa using hy, ?_⟩
    have := lt_add hy1 hz
    rw [← norm_neg] at this
    have e : ((-Units.mk0 y hy0 : (Qbar l)ˣ) : Qbar l) - z = -(y - 1 + ((z : Qbar l) - ((-1 : (Qbar l)ˣ) : Qbar l))) := by
      rw [Units.val_neg, Units.val_neg, Units.val_mk0, Units.val_one]
      ring
    rw [Cong, e]
    exact this
end
private theorem indEx (hP : MixOfP) :
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D),
    D.Good → T.Ok → T.Two → T.Deep → ∀ ι : Qbar l ≃+* ℂ,
    ∃ (k₀ : IntermediateField ℚ Ω) (_ : NumberField k₀) (_ : IsTotallyReal k₀) (φ : G ℚ Ω →* (Qbar l)ˣ) (k t : ℕ)
      (r : G k₀ Ω →* GL (Fin 2) (Qbar l)) (α β : (Qbar l)ˣ) (R : G ℚ Ω →* GL (Fin 4) (Qbar l)) (δ : G T.F Ω →* (Qbar l)ˣ),
      IndDat T k₀ φ ι k t r α β R δ ∧ PR ι r := by
  intro Ω _ _ _ l _ c D T hg hok h2 hd ι
  obtain ⟨k₀, _, _, φ, hyp, hrange, hidx, hemb⟩ := UpperTheory.exists_quadratic_character_of_subgroup_index_two Ω l c D T hg hok h2 hd
  have hc := UpperTheory.galois_character_residual_decomposition Ω l c D T k₀ φ hyp
  obtain ⟨k, t, r₀, dat₀, hrw⟩ := hP Ω l c D T k₀ φ ι hyp hc
  obtain ⟨u, hu⟩ : resQ T.F T.g0 * resQ T.F T.g0 ∈ (resQ k₀).range := hrange ▸ Subgroup.mul_self_mem_of_index_two hidx _
  obtain ⟨r, iso, h01, h10, rib, ns⟩ := UpperTheory.exists_ribet_lattice Ω l c D T k₀ φ ι k t r₀ hyp hc dat₀ u hu
  have dat := UpperTheory.galoisRep_properties_invariant_under_conjugation Ω l k₀ ι _ k t r₀ r dat₀ iso
  set μ : G ℚ Ω →* (Qbar l)ˣ := cycBar ℚ Ω l ^ k * up D.ξ * φ with hμ
  have hF : ∀ g : G T.F Ω, resQ T.F g ∈ T.F.fixingSubgroup := fun g => by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    exact fun x hx => g.commutes ⟨x, hx⟩
  have hdet : ∀ h, Matrix.GeneralLinearGroup.det (r h) = μ (resQ k₀ h) := fun h => by
    have e := DFunLike.congr_fun dat.det h
    have e' : φ (resQ k₀ h) = 1 := hyp.φ_in _ (hrange ▸ ⟨h, rfl⟩)
    simp only [hμ, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.comp_apply, e', mul_one] at e ⊢
    rw [e]
    rfl
  have ru := rib u (by rw [hu, ← map_mul]; exact hF _)
  obtain ⟨α, hα, hαc⟩ := root_ex ru.1 hc.c3
  have hmu := hc.mult k dat.dvd
  have hμ1 : ∀ g : G T.F Ω, ‖(μ (resQ T.F g) : Qbar l)‖ = 1 := fun g =>
    norm_of_cong (by rw [norm_sub_rev]; exact hmu g) (hc.unit _ _)
  have hα1 : ‖(α : Qbar l)‖ = 1 := norm_of_cong hαc (hc.unit _ _)
  obtain ⟨R, hR, hgsp⟩ := UpperTheory.symmetric_square_mixed_exists (Qbar l) _ _ (resQ k₀) (resQ T.F T.g0) α (μ (resQ T.F T.g0) / α) r μ two_ne_zero
    hemb.injective (hrange ▸ hidx) (hrange ▸ hc.out) (fun u' hu' => by
      obtain rfl : u' = u := hemb.injective (hu'.trans hu.symm)
      have e := congrArg Units.val (hdet u')
      rw [hu, map_mul, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h01, h10, ← hα, Units.val_mul] at e
      ext i j
      fin_cases i <;> fin_cases j
      · simp [hα]
      · simp [h01]
      · simp [h10]
      · have := α.ne_zero
        simp only [Fin.mk_one, Fin.isValue, Matrix.diagonal_apply_eq, Matrix.cons_val_one, Matrix.cons_val_fin_one,
          Units.val_div_eq_div_val]
        field_simp
        linear_combination e) hdet (mul_div_cancel _ _)
  have hres : Continuous (resQ T.F) := (emb ℚ T.F Ω).continuous
  obtain ⟨δ, hδc, hδ2, hδ1⟩ := UpperTheory.exists_square_root_of_character_near_one l hg.l_odd _ ((up D.th / μ).comp (resQ T.F)) ((hc.cont k).comp hres) fun g => by
    have := (μ (resQ T.F g)).ne_zero
    have e : (((up D.th / μ).comp (resQ T.F) g : (Qbar l)ˣ) : Qbar l) - ((1 : (Qbar l)ˣ) : Qbar l) =
        ((up D.th (resQ T.F g) : Qbar l) - μ (resQ T.F g)) / μ (resQ T.F g) := by
      rw [MonoidHom.comp_apply, MonoidHom.div_apply, Units.val_div_eq_div_val, Units.val_one, sub_div, div_self this]
    rw [Cong, e, norm_div, hμ1, div_one]
    exact hmu g
  haveI : FaithfulSMul k₀ Ω := (faithfulSMul_iff_algebraMap_injective k₀ Ω).2 (algebraMap k₀ Ω).injective
  haveI : Module.IsTorsionFree k₀ Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure k₀ Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  refine ⟨k₀, ‹_›, ‹_›, φ, k, t, r, α, _, R, δ, ⟨hyp, hc, dat, rib, ns, hR,
    UpperTheory.continuous_mix_family l _ _ _ _ _ _ r R hR hemb dat.cont, hgsp, hαc, ?_, hδc, fun g => ?_, hδ1⟩, prIso k₀ Ω l ι 2 r₀ r iso hrw⟩
  · have e0 := congrArg Units.val (hc.mul 0 (resQ T.F T.g0))
    have := α.ne_zero
    have e : ((μ (resQ T.F T.g0) / α : (Qbar l)ˣ) : Qbar l) - ch T 0 (resQ T.F T.g0) =
        (-((up D.th (resQ T.F T.g0) : Qbar l) - μ (resQ T.F T.g0)) +
          -(ch T 0 (resQ T.F T.g0) * ((α : Qbar l) - ch T 3 (resQ T.F T.g0)))) / α := by
      rw [← e0, Units.val_div_eq_div_val, Units.val_mul, show (0 : Fin 4).rev = 3 from rfl]
      field_simp
      ring
    rw [Cong, e, norm_div, hα1, div_one]
    refine lt_add (by rw [norm_neg]; exact hmu _) ?_
    rw [norm_neg, norm_mul, hc.unit, one_mul]
    exact hαc
  · rw [hδ2, MonoidHom.comp_apply, MonoidHom.div_apply, div_mul_cancel]
theorem UpperTheory.V.Z.Bc.seedII_of_p_alt :
    MixOfP → IndAutLP → _root_.UpperTheory.V.Ws.SeedIIAlt := by
  intro hP hI Ω _ _ _ l _ c D T hctx hok h2 hd ι
  obtain ⟨k₀, _, _, φ, k, t, r, α, β, R, δ, h, hrw⟩ := indEx hP Ω l c D T hctx.1 hok h2 hd ι
  have hirr : IsIrr ((R.comp (resQ T.F)).comp T.G'.subtype) := UpperTheory.induced_irreducible Ω l c D T k₀ φ ι k t r α β R δ h
  obtain ⟨n, hloc, m, b, N, hm, hw, hN, hfin⟩ := indLoc0 Ω l c D T k₀ φ ι k t r α β R δ h
  obtain ⟨⟨π, hreg, hatt⟩, hW⟩ := hI Ω l c D T k₀ φ ι k t r α β R δ h hrw
  refine _root_.UpperTheory.induced_final_statement_alt Ω l c D T ι ⟨twF T R δ, n⟩ (indGlob_of_kill UpperTheory.induced_representation_constituent_vanishing Ω l c D T k₀ φ ι k t r α β R δ h) hloc ⟨?_, ?_⟩
  · rw [(irrIff _).1]
    have := (shapeFacts l _ 4 _ (δ.comp T.G'.subtype)).2.2.2.2.2 hirr
    convert this using 1
    ext g : 2
    rfl
  · have hcont : Continuous (resLe T.F_le) := by
      rw [(emb ℚ T.F Ω).continuous_iff]
      exact (emb ℚ T.L Ω).continuous
    refine ⟨fun i => 2 * m i + b, (δ.comp (resLe T.F_le))⁻¹, π, -b, N, fun i => ⟨m i.castSucc - m i.succ, by linarith [hm i], by ring⟩,
      hw, (h.δ_cont.comp hcont).inv, hN, ⟨m 0, by ring⟩, fun A _ s _ => ?_, _root_.UpperTheory.V.Z.Win.Birth.mkReg' hreg (hW π hreg hatt), ?_⟩
    · have e := hfin (resLe T.F_le s)
      have e' : cycBar T.L Ω l s = cycBar T.F Ω l (resLe T.F_le s) := rfl
      rw [← inv_eq_one, ← inv_pow, ← e, e']
      simp [mul_comm]
    · convert hatt using 1
      ext g : 2
      rw [tw_val]
      change _ • (tw (R.comp (resQ T.F)) δ (resLe T.F_le g)).val = _
      rw [tw_val, smul_smul]
      simp
      rfl
end
end

section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Sd
open private attR_tw_cyc norm_of_cong U1 cong_iff cyc_mem ordAt_tw irrOpen_of cont_units from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.BaseChangeNorms.MixSeed
theorem UpperTheory.V.Z.Win.Birth.mix_birth_of_prints :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.Esk.PropMV → UpperTheory.V.Z.Win.Birth.MixSeedP := by
  classical
  rintro hP hM F Ω _ _ _ _ _ _ l _ hl hev hsp ι ξ hξ hodd hunr ⟨u, Au, hu2, hAu, hur⟩ hsq hdec P ⟨w₁, hw₁, hl₁⟩ ⟨w₂, hw₂, hl₂⟩
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have hv : ∀ {w : Pl F} {A : ValuationSubring Ω}, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → IsPlaceOver A w →
      A.valuation (l : Ω) < 1 := fun h hA => by simpa using (hA _).2 h
  have hn : ∀ g, ‖(ξ g : Qbar l)‖ = 1 := fun g => by
    have : Finite (G F Ω ⧸ ξ.ker) := Subgroup.quotient_finite_of_isOpen _ hξ
    have h0 : ξ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h1 : ξ g ^ ξ.ker.index = 1 := by rw [← map_pow]; exact ξ.ker.pow_index_mem g
    have h2 : ‖(ξ g : Qbar l)‖ ^ ξ.ker.index = 1 := by rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1]; simp
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) h0).1 h2
  obtain ⟨A₁, hA₁⟩ := exists_isPlaceOver Ω w₁
  obtain ⟨A₂, hA₂⟩ := exists_isPlaceOver Ω w₂
  have hF2 : 2 ≤ Module.finrank ℚ F := by
    have h0 : 0 < Module.finrank ℚ F := Module.finrank_pos
    obtain ⟨j, hj⟩ := hev
    omega
  obtain ⟨k, t, hk2, ht2, hkl, htl, c, a, π₁, r₁, h₁, hres₁, ha⟩ := hM F Ω l hl hF2 hsp ι ξ hξ hodd hunr ⟨u, Au, hu2, hAu, hur⟩ P
    ⟨w₁, hw₁, hl₁, A₁, hA₁, hdec A₁ (hv hl₁ hA₁)⟩ ⟨w₂, hw₂, hl₂, A₂, hA₂, hdec A₂ (hv hl₂ hA₂)⟩
  have hkz : (l : ℤ) - 1 ∣ k := by
    rw [← Nat.cast_pred (Fact.out : l.Prime).pos]
    exact Int.natCast_dvd_natCast.2 hkl
  have htz : (l : ℤ) - 1 ∣ t := by
    rw [← Nat.cast_pred (Fact.out : l.Prime).pos]
    exact Int.natCast_dvd_natCast.2 htl
  let m : Pl F → Fin 2 → ℤ := fun w => if w ∈ P then ![(t : ℤ), -(k : ℤ) - t] else ![0, -(k : ℤ)]
  have hm₁ : ∀ w ∈ P, m w = ![(t : ℤ), -(k : ℤ) - t] := fun w h => if_pos h
  have hm₂ : ∀ w ∉ P, m w = ![0, -(k : ℤ)] := fun w h => if_neg h
  replace h₁ : OrdForm ι ξ (-(k : ℤ)) c m a π₁ r₁ := h₁
  obtain ⟨π, hatt, hinf⟩ := attR_tw_cyc h₁.att k
  have SF := shapeFacts l (G F Ω) 2 r₁ (cycBar F Ω l ^ k)
  have hU : ∀ g : G F Ω, cycBar F Ω l g ^ k ∈ U1 l := fun g => by simpa using cyc_mem g hkz
  have hn' : ∀ i g, ‖(((![1, ξ] : Fin 2 → G F Ω →* (Qbar l)ˣ) i g : (Qbar l)ˣ) : Qbar l)‖ = 1 :=
    Fin.forall_fin_two.2 ⟨fun g => by simp, hn⟩
  have hres : ResSum (tw r₁ (cycBar F Ω l ^ k)) ![1, ξ] := by
    refine (shapeFacts l (G F Ω) 2 _ 1).2.2.2.2.1 _ _ 1 (fun i g => ?_)
      (SF.2.2.2.1 _ (fun g => norm_of_cong (hU g)) hres₁) fun i g => ?_
    · rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hn', one_mul]
      exact norm_of_cong (hU g)
    · rw [Cong, norm_sub_rev]
      refine (cong_iff (hn' i g)).2 ?_
      rw [MonoidHom.mul_apply, Equiv.Perm.one_apply, mul_inv_cancel_comm]
      exact hU g
  have hO := _root_.UpperTheory.V.Z.Win.RR.ordAbove_of_printsH hP F Ω l hl hsp ι ξ _ c m a π₁ r₁ h₁
  have hO₁ : ∀ w ∈ P, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ A, IsPlaceOver A w →
      OrdAt (tw r₁ (cycBar F Ω l ^ k)) ![(k : ℤ) + t, -(t : ℤ)] ![ξ, 1] A := fun w h hw A hA => by
    obtain ⟨κ, h1, h2, h3⟩ := hO w hw A hA
    have := ordAt_tw (ψ₀ := ξ) (ψ₁ := 1) h₁.cont hkz.neg_right (by rw [mul_one]; exact h₁.det)
      (continuous_of_isOpen_ker' ξ hξ) hn (fun g => by simp) hA (hunr A (hv hw hA)) (by rw [hm₁ w h]; exact htz) h1 h2
      (fun σ hσ => by rw [Cong, ← (ha w hw A hA σ hσ).1 h]; exact h3 σ hσ) hkz
    convert this using 1
    rw [hm₁ w h]
    ext i
    fin_cases i <;> simp <;> ring
  have hO₂ : ∀ w ∉ P, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ A, IsPlaceOver A w →
      OrdAt (tw r₁ (cycBar F Ω l ^ k)) ![(k : ℤ), 0] ![1, ξ] A := fun w h hw A hA => by
    obtain ⟨κ, h1, h2, h3⟩ := hO w hw A hA
    have := ordAt_tw (ψ₀ := 1) (ψ₁ := ξ) h₁.cont hkz.neg_right (by rw [one_mul]; exact h₁.det)
      continuous_const (fun g => by simp) hn hA (fun _ _ => rfl) (by rw [hm₂ w h]; exact dvd_zero _) h1 h2
      (fun σ hσ => by
        have h4 := h3 σ hσ
        rw [(ha w hw A hA σ hσ).2 h] at h4
        exact h4) hkz
    convert this using 1
    rw [hm₂ w h]
    ext i
    fin_cases i <;> simp
  refine ⟨k, t, π, tw r₁ (cycBar F Ω l ^ k), hk2, ht2, hkl, htl, ?_, ?_, hatt, ?_, hres,
    ⟨fun A hA => ?_, UpperTheory.V.Z.Win.Birth.prTw F Ω l ι r₁ _ (by
      simpa using (_root_.UpperTheory.V.Sd.alg_cyclotomic_of_printed_results hP.toClassicalTheorems F Ω l ι).1 (k : ℤ) 1 (by simp)) (UpperTheory.V.Z.Win.Birth.prOrd F Ω l ι ξ _ c m a π₁ r₁ h₁)⟩,
    fun w hw => ⟨fun h => ⟨hO₁ w h hw, fun τ hτ => ?_⟩, fun h => ⟨hO₂ w h hw, fun τ hτ => ?_⟩⟩⟩
  · have hz : Continuous fun s : G F Ω => ((cycZ F Ω l s : ℤ_[l]ˣ) : ℤ_[l]) :=
      Units.continuous_val.comp (continuous_cycZ F Ω l)
    have hcyc : Continuous fun s : G F Ω => (cycBar F Ω l s : Qbar l) :=
      (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp (continuous_subtype_val.comp hz)
    refine cont_units _ ?_
    simp only [tw_val, MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
    exact (hcyc.pow k).smul (Units.continuous_val.comp h₁.cont)
  · have hk0 : (k : ℤ) ≠ 0 := by omega
    exact irrOpen_of hl hn (SF.2.2.2.2.2 (_root_.UpperTheory.V.Sd.ordinary_irreducible_of_printed_hida hP F Ω l hl hsp ι ξ _ c m a π₁ r₁ h₁)) hres hsq (hv hl₂ hA₂)
      hk0 (hO₂ w₂ hw₂ hl₂ A₂ hA₂)
  · refine MonoidHom.ext fun g => Units.ext ?_
    have h2 : Matrix.GeneralLinearGroup.det (r₁ g) = cycBar F Ω l g ^ (-(k : ℤ)) * ξ g := DFunLike.congr_fun h₁.det g
    have h3 := congrArg Units.val h2
    rw [Matrix.GeneralLinearGroup.val_det_apply] at h3
    rw [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.val_det_apply, tw_val, Matrix.det_smul, h3]
    simp only [zpow_neg, zpow_natCast, MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_inv_eq_inv_val,
      Fintype.card_fin]
    field_simp
  · refine (shapeFacts l (G F Ω) 2 _ 1).2.1 _ _ _ 1 (SF.1 _ _ (_root_.UpperTheory.V.Z.Win.RR.ordAway_a_alt hP F Ω l ι ξ _ c m a π₁ r₁ h₁ A hA))
      fun i s hs => ?_
    have h1 : cycZ F Ω l s = 1 := (UpperTheory.V.Base.places F Ω l A).2.2.2 hA hs
    rw [MonoidHom.mul_apply, MonoidHom.pow_apply, cycBar, MonoidHom.comp_apply, h1, map_one, one_pow, mul_one]
    rfl
  · convert hinf _ _ ((h₁.above w hw).2.2.2.2.2 τ hτ) using 2
    rw [hm₁ w h]
    ext i
    fin_cases i <;> simp <;> ring
  · convert hinf _ _ ((h₁.above w hw).2.2.2.2.2 τ hτ) using 2
    rw [hm₂ w h]
    ext i
    fin_cases i <;> simp
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd
namespace UpperTheory.Esk.PropMVAux
variable {l : ℕ} [Fact l.Prime]
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
end UpperTheory.Esk.PropMVAux
open UpperTheory.Esk.PropMVAux in
open Classical in
theorem UpperTheory.Esk.pf_PropMV_sv_alt : _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Sd.PropMHol → UpperTheory.Esk.HolWC → UpperTheory.Esk.HRep → UpperTheory.Esk.PropMV := by
  intro hPH hMH hWC hHR F Ω _ _ _ _ _ _ l _ hl2 hd hsplit ι ξ ho hodd hunr hram P hP1 hP2
  have : IsGalois F Ω := {}
  obtain ⟨art, ha⟩ := hPH.litN.aut.art F Ω
  have hc := continuous_of_isOpen_ker' ξ ho
  have : Finite (G F Ω ⧸ ξ.ker) := ξ.ker.quotient_finite_of_isOpen ho
  have hm : 0 < ξ.ker.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hξm : ξ ^ ξ.ker.index = 1 := MonoidHom.ext fun g => by
    rw [MonoidHom.pow_apply, ← map_pow]
    exact ξ.ker.pow_index_mem g
  have hn : ∀ s, ‖(ξ s : Qbar l)‖ = 1 := fun s => by
    have h2 : ξ s ^ ξ.ker.index = 1 := DFunLike.congr_fun hξm s
    have h3 : ‖(ξ s : Qbar l)‖ ^ ξ.ker.index = 1 := by rw [← norm_pow, ← Units.val_pow_eq_pow_val, h2]; simp
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 h3
  obtain ⟨ω, ⟨hω, hL⟩, -⟩ := exists_unique_hchar_of_finite_order ha ι ξ hc hm hξm
  have hfo : IsOfFinOrder ω := isOfFinOrder_iff_pow_eq_one.2 ⟨_, hm, hω⟩
  obtain ⟨c, hcond, hc0, hfin⟩ := cond_ex ω hm hω
  have hine : ∀ (w : Pl F) (A : ValuationSubring Ω), IsPlaceOver A w → (Ine (F := F) A ≤ ξ.ker ↔ c w = 0) := fun w A hA =>
    (hL.unr_iff ha (Or.inr rfl) hA).trans (hc0 w).symm
  have hcl : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → c w = 0 := fun w hw => by
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    exact (hine w A hA).1 (hunr A (by simpa using (hA _).2 hw))
  have hfr : ∀ (w : Pl F), c w = 0 → ∀ A, IsPlaceOver A w → ∀ σ : G F Ω, IsFrob A (normV w) σ →
      ι.symm (ω.val w : ℂˣ) = (ξ σ⁻¹ : (Qbar l)ˣ) := fun w hw A hA σ hσ => by
    rw [map_inv, Units.val_inv_eq_inv_val, hL.frob_unr ha (Or.inr rfl) ((hc0 w).1 hw) hA hσ, inv_inv]
  have hsg : ∀ v, ω.locInf v (-1) = -1 := fun v => by
    obtain ⟨j, σ, hσ, rfl⟩ := GlobalTheory.HilbertFromArtin.exists_conj (Ω := Ω) v (IsTotallyReal.isReal v)
    have e := hL _ σ (GlobalTheory.HilbertFromArtin.art_sign_eq ha j σ hσ)
    rw [infPow_zero, lPow_zero, inv_one, mul_one, mul_one, hodd σ ⟨j, hσ⟩] at e
    refine Units.ext (ι.symm.injective (e.symm.trans ?_))
    simp
  have hex : ∃ w, c w ≠ 0 := by
    obtain ⟨u, A, -, hA, hnA⟩ := hram
    exact ⟨u, fun h => hnA ((hine u A hA).2 h)⟩
  have hnc : ∀ w : Pl F, (((l : ℕ) : 𝓞 F) ∈ w.asIdeal ∧ ∃ A, IsPlaceOver A w ∧ ∃ σ ∈ Dec (F := F) A, ¬ Cong (ξ σ) 1) →
      ((l : ℕ) : 𝓞 F) ∈ w.asIdeal ∧ ¬ ‖ι.symm (ω.val w : ℂˣ) - 1‖ < 1 := by
    rintro w ⟨hw, A, hA, σ, hσ, h⟩
    exact ⟨hw, fun h' => h (dec_cong ha hc hL ((hc0 w).1 (hcl w hw)) h' hA hσ)⟩
  obtain ⟨k, hkB, hk, φ, lam, hφ, hcu, hlam⟩ := hMH F l hl2 ι ω c hfo hsg hcond hex hcl P
    (hP1.imp fun w h => ⟨h.1, hnc w h.2⟩) (hP2.imp fun w h => ⟨h.1, hnc w h.2⟩) 3
  have hlev : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → levL l c w = c w := fun w hw => if_neg hw
  have hlev1 : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → levL l c w = 1 := fun w hw => if_pos hw
  have hfinL : {w | levL l c w ≠ 0}.Finite := by
    refine (hfin.union (fin_l (l := l))).subset fun w hw => ?_
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
    exact hw ((hlev w h.2).trans h.1)
  have heu : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ‖ι.symm (eisT l ω c P w)‖ = 1 := fun w hw => by
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    obtain ⟨σ, hσ⟩ := exists_isFrob hA
    rw [eisT, if_pos hw]
    split_ifs
    · rw [hfr w (hcl w hw) A hA σ hσ, hn]
    · simp
  obtain ⟨D⟩ := Wc.exL F l ι hsplit
  have hu2 : ∃ u, levL l c u ≠ 0 ∧ normV u = 2 := by
    obtain ⟨u, A, h2, hA, hnA⟩ := hram
    refine ⟨u, ?_, h2⟩
    by_cases hl : ((l : ℕ) : 𝓞 F) ∈ u.asIdeal
    · rw [hlev1 u hl]; exact one_ne_zero
    · rw [hlev u hl]; exact fun h => hnA ((hine u A hA).2 h)
  have hunit : ∀ v, Wc.nu ι (lam (D.pl v)) = 1 := fun v => by
    rw [nu_eq]
    refine norm_eq_one (heu _ (D.mem v)) ?_
    rw [← map_sub]
    exact hlam _
  obtain ⟨t, htB, ht, φ', lam', hV, hne, hcusp, heig, hcong⟩ :=
    hWC F hd l hl2 ι D (k + 1) (by omega) (levL l c) hfinL (fun v => hlev1 _ (D.mem v)) hu2 ω hfo φ lam hφ hcu hunit
      {v | D.pl v ∈ P} 2
  have hlam' : ∀ w, ‖ι.symm ((∏ v, if D.pl v = w ∧ v ∈ {v | D.pl v ∈ P} then (l : ℂ) ^ t else 1) * lam' w -
      eisT l ω c P w)‖ < 1 := fun w => by
    rw [← sub_add_sub_cancel _ (lam w), map_add]
    exact add_lt (nu_lt.1 (hcong w)) (hlam w)
  have haway : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ‖ι.symm (lam' w - eisT l ω c P w)‖ < 1 := fun w hw => by
    have h := hlam' w
    rwa [prod_away D _ t w hw, one_mul] at h
  obtain ⟨π, hreg, ⟨χ, hpol⟩, hinf, hU, hsat⟩ := hHR F (k + 1) (by omega) (fun v => if v ∈ {v | D.pl v ∈ P} then t else 0)
    (levL l c) ω hfo φ' lam' hV hne heig hcusp
  obtain ⟨r, wt, HT, hG, hatt, -⟩ := _root_.UpperTheory.Gal.SV.exRS_alt hPH.toClassicalTheorems F Ω l ι 2 one_le_two π χ hreg hpol
  obtain ⟨hdet, hres⟩ := det_res ξ hc r hG.cont k hk hn
    (((Filter.eventually_cofinite.1 hatt.2).union hfin).union (fin_l (l := l))) fun w hw A hA σ hσ => by
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hw
      obtain ⟨⟨⟨B₁, hB₁, hF⟩, h0⟩, hl⟩ := hw
      obtain ⟨B₂, hB₂, e⟩ := hsat w ((hlev w hl).trans h0)
      obtain rfl := hB₁.unique hB₂
      obtain ⟨h2, h3⟩ := tr_det ι _ _ _ (((hF A hA).2 σ hσ).trans e)
      have h4 := haway w hl
      rw [eisT, if_neg hl, if_pos h0, map_sub, map_add, map_one, hfr w h0 A hA σ hσ] at h4
      rw [h2, h3, map_mul, hfr w h0 A hA σ hσ, map_pow, map_natCast, cyc_frob hl hA hσ]
      exact ⟨h4, rfl⟩
  refine ⟨k, t, by omega, htB, hk, ht, levL l c, fun w => ι.symm (eisT l ω c P w), π, r,
    ⟨hreg, ⟨χ, hpol⟩, hG.cont, hatt, hdet, ho, hfinL, fun w A hA => ?_, fun w hw => ?_, fun w hw hl => ?_, fun w hw => ?_⟩,
    hres, fun w hw A hA σ hσ => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [hine w A hA]
    by_cases hl : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal
    · simp [hl, hcl w hl]
    · simp [hl, hlev w hl]
  · obtain ⟨v, h1, h2, -⟩ := hU w
    rw [hw] at h2
    exact ⟨v, h1, h2⟩
  · refine ⟨lam' w, hU w, norm_one_of ?_⟩
    have h4 := haway w hl
    rwa [eisT, if_neg hl, if_neg (hlev w hl ▸ hw), map_sub, map_one] at h4
  · obtain ⟨v₀, hv₀⟩ := D.surj w hw
    have hnorm : normV w = l := hv₀ ▸ D.norm v₀
    have hc' := hlam' w
    rw [prod_at D _ t w v₀ hv₀] at hc'
    refine ⟨hlev1 w hw, ?_, ?_, heu w hw, ⟨lam' w, hlev1 w hw ▸ hU w, ?_⟩, fun τ hτ => ?_⟩
    · by_cases h : w ∈ P <;> simp [h] <;> omega
    · by_cases h : w ∈ P <;> simp [h] <;> ring
    · rw [hnorm]
      by_cases h : w ∈ P
      · have hv : v₀ ∈ {v | D.pl v ∈ P} := by simpa [hv₀] using h
        rw [if_pos hv, map_sub, map_mul, map_pow, map_natCast, mul_comm] at hc'
        rw [if_pos h]
        simpa using hc'
      · have hv : v₀ ∉ {v | D.pl v ∈ P} := by simpa [hv₀] using h
        rw [if_neg hv, one_mul, map_sub] at hc'
        rw [if_neg h]
        simpa using hc'
    · obtain ⟨v, hvd⟩ : ∃ v, InfinitePlace.mk (ι.toRingHom.comp τ) = v := ⟨_, rfl⟩
      have hv : D.pl v = w := hvd ▸ (D.embAt τ w).1 hτ
      rw [hvd]
      convert hinf v using 3
      by_cases h : w ∈ P
      · have hS : v ∈ {v | D.pl v ∈ P} := by simpa [hv] using h
        ext i; fin_cases i <;> simp [h, hS] <;> omega
      · have hS : v ∉ {v | D.pl v ∈ P} := by simpa [hv] using h
        ext i; fin_cases i <;> simp [h, hS] <;> omega
  · simp only [eisT, if_pos hw, if_pos h]
    exact hfr w (hcl w hw) A hA σ hσ
  · simp only [eisT, if_pos hw, if_neg h, map_one]
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Polynomial UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd Matrix
open GlobalTheory.CuspRep (SmIrr Af invT finId pFin locGL finGL GA chiDet)
namespace UpperTheory.Esk.HeckeRepresentationSatake
section Proj
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ}
theorem exists_sat_alt (P : _root_.UpperTheory.V.Af.Hypotheses') (π : TR.CuspSub F a) (w : HeightOneSpectrum (𝓞 F))
    (h : HasFixed (π.locRep w) (GlobalTheory.LFun.KGL w a)) : ∃ B, π.HasSat w B := by
  obtain ⟨⟨σ, hσ⟩, h2⟩ := _root_.UpperTheory.V.Af.local_comp_real_of_printed_results P F a π w
  have hi := h2 σ hσ
  obtain ⟨h3, h4⟩ := _root_.UpperTheory.V.Af.satake_local_of_printed_results P F a w σ
  obtain ⟨x, hx0, hx⟩ := h
  obtain ⟨B, hB⟩ := h3 (GlobalTheory.CuspRep.LocSph.exists_fixed_of_mem_iSup (π.locRep w) σ.ρ σ.irred
    (fun f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.finPart (locGL F a w g) (f v)} => f.1) (fun f => f.2)
    (GlobalTheory.LFun.KGL w a : Set _) x hx0 hx (hi.2 ▸ Submodule.mem_top))
  exact ⟨B, (h4 _ _ hi B).2 hB⟩
end Proj
section Loc
open GlobalTheory.LFun Formalism.UG
variable {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))
end Loc
section Inf
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
open GlobalTheory.HeckeGal.Model GlobalTheory.Mem.Chr.CharModel
end Inf
section Sign
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
end Sign
theorem _root_.UpperTheory.Esk.pf_HRep_alt : _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.Esk.HCap → UpperTheory.Esk.HRep := by
  intro P hC
  unfold UpperTheory.Esk.HCap at hC
  unfold UpperTheory.Esk.HRep
  intro F _ _ _ k hk t c ω hω φ lam hφ hne heig hcusp
  obtain ⟨h1, hcap⟩ := hC F (fun v => k + 2 * t v) c ω hω φ hφ
  obtain ⟨π₀, ψ, hψ, h0, hz⟩ := proj hne (P.ssR F 2 φ hcusp ⟨0, by rw [h1, zero_smul]⟩)
  set ν := GlobalTheory.HeckeGal.Model.absPow F (1 - (k : ℝ) / 2) with hν
  obtain ⟨hν1, hν2, -⟩ := GlobalTheory.HeckeGal.Model.absPow_isAbsPow F (1 - (k : ℝ) / 2)
  rw [← hν] at hν1 hν2
  have hq : ∀ w : Pl F, (0 : ℝ) < normV w := fun w =>
    Nat.cast_pos.2 (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm w))
  have hν3 : ∀ w, ((ν.val w : ℂˣ) : ℂ) = (((normV w : ℝ) ^ ((k : ℝ) / 2 - 1) : ℝ) : ℂ) := fun w => by
    rw [hν2, Complex.ofReal_cpow (hq w).le, ← Complex.ofReal_neg, neg_sub]
    rfl
  set π := π₀.twist ν
  set x₀ : π₀.V := ⟨ψ, hψ⟩
  set T := π₀.toTwist ν
  have hx0 : T x₀ ≠ 0 := (map_ne_zero_iff _ T.injective).2 fun e => h0 (congrArg Subtype.val e)
  have hact : ∀ w g y, π.locRep w g (T y) = ((ν.loc w (GeneralLinearGroup.det g) : ℂˣ) : ℂ) • T (π₀.locRep w g y) :=
    fun w g y => (TR.CuspSub.finPart_toTwist ν _ y).trans (by rw [TR.CuspSub.chiDet_locGL]; rfl)
  have hloc : ∀ w g (a : ℂ), locSm F w g φ = a • φ → π₀.locRep w g x₀ = a • x₀ := fun w g a h =>
    Subtype.ext (hz _ (fun V hV => hV (.fin (locGL F 2 w g))) a h)
  have hfix₀ : ∀ w, x₀ ∈ Hi.fixd (π₀.locRep w) (K1 w (c w)) := fun w u hu =>
    (hloc w u 1 ((hφ.level w u hu).trans (one_smul _ _).symm)).trans (one_smul _ _)
  have hfix : ∀ w, T x₀ ∈ Hi.fixd (π.locRep w) (K1 w (c w)) := fun w u hu => by
    rw [hact, hν1 w _ (unit_det w hu), hfix₀ w u hu, Units.val_one, one_smul]
  have hU : ∀ w, Uop w (π.locRep w) (c w) (T x₀) = lam w • T x₀ := fun w => by
    have h2 := hz (Sd.hk k w (c w)) (fun V hV y hy => V.smul_mem _
      (finsum_induction (fun z : Module.End ℂ (TR.Sm F 2) => z y ∈ V) V.zero_mem (fun _ _ => V.add_mem)
        fun q => hV (.fin _) y hy)) _ (heig w)
    have h3 := uop_map w (ρ' := locSm F w) π₀.V.subtype 1 (fun g y => (one_smul _ _).symm) (c w) x₀ (hfix₀ w)
      fun u hu => congrArg Subtype.val (hfix₀ w u hu)
    refine (uop_map w T.toLinearMap (ν.loc w) (hact w) (c w) x₀ (hfix₀ w) (hfix w)).trans ?_
    rw [LinearEquiv.coe_coe, ← map_smul T, ← map_smul T]
    refine congrArg T (Subtype.ext ?_)
    refine Eq.trans ?_ h2
    change ((ν.val w : ℂˣ) : ℂ) • π₀.V.subtype (Uop w (π₀.locRep w) (c w) x₀) =
      (((normV w : ℝ) ^ ((k : ℝ) / 2 - 1) : ℝ) : ℂ) • Uop w (locSm F w) (c w) (π₀.V.subtype x₀)
    rw [h3, hν3]
    exact congrArg _ (one_smul _ _).symm
  have hZ : ∀ w, π.locRep w (GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))) (T x₀) =
      (((ω * ν * ν).val w : ℂˣ) : ℂ) • T x₀ := fun w => by
    rw [hact, hloc w _ (ω.val w : ℂˣ) (Subtype.ext (funext fun g => by
      change φ.1 (g * finGL F 2 (locGL F 2 w _)) = _
      rw [fin_scalar, ← GlobalTheory.CuspRep.scalar_comm, hφ.cent]
      rfl)), map_smul, smul_smul,
      show GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))) =
        atFin w (unif w) * atFin w (unif w) from Units.ext (by simp [sq]), map_mul, mul_comm, ← Units.val_mul, ← mul_assoc]
    rfl
  have hsat : ∀ w, (∀ u ∈ GlobalTheory.LFun.KGL w 2, π.locRep w u (T x₀) = T x₀) → ∃ α β : ℂˣ, π.HasSat w {α, β} ∧
      Uop w (π.locRep w) 0 (T x₀) = ((((normV w : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (α + β)) • T x₀ ∧
      α * β = (ω * ν * ν).val w := fun w h => by
    obtain ⟨B, hB⟩ := _root_.UpperTheory.Esk.HeckeRepresentationSatake.exists_sat_alt P.toClassicalTheorems π w ⟨_, hx0, h⟩
    obtain ⟨α, β, rfl, h2, h3⟩ := sat_two w (hB.2 _ (GlobalTheory.LGrp.mem_fixed.2 h) hx0)
    exact ⟨α, β, hB, h2, Units.ext (smul_left_injective ℂ hx0 (h3.symm.trans (hZ w)))⟩
  have hinf : ∀ v, π.HasInfChar v (infOf ![(t v : ℤ), 1 - (k : ℤ) - t v]) := fun v => by
    have h2 : π₀.HasInfChar v {(((k + 2 * t v : ℕ) : ℂ) - 1) / 2, -((((k + 2 * t v : ℕ) : ℂ) - 1) / 2)} :=
      ⟨rfl, fun u => cap_all π₀ hψ h0 v u _ (by
        rw [hz _ (fun V hV => TR.Zalg_stable (fun X => hV (.lie X)) (Algebra.subset_adjoin ⟨v, u, rfl⟩)) _ (hcap v u)]
        simp [sub_eq_add_neg])⟩
    convert h2.twist ν using 1
    rw [hν, expo_abs]
    simp only [infOf, Fin.univ_val_map, List.ofFn_succ, List.ofFn_zero, Multiset.insert_eq_cons, Multiset.map_cons,
      Multiset.map_singleton]
    change _ ::ₘ ({_} : Multiset ℂ) = _
    refine congrArg₂ _ ?_ (congrArg _ ?_) <;> simp <;> ring
  refine ⟨π, fun v => ⟨_, hinf v, ?_, fun z hz => ?_⟩, ⟨ω * ν * ν, fun v v' => ?_, ?_⟩, hinf,
    fun w => ⟨_, hx0, hfix w, hU w⟩, fun w hw => ?_⟩
  · refine Multiset.Nodup.map (fun i j e => ?_) Finset.univ.nodup
    have e' : ![(t v : ℤ), 1 - (k : ℤ) - t v] i = ![(t v : ℤ), 1 - (k : ℤ) - t v] j := by exact_mod_cast add_left_cancel e
    fin_cases i <;> fin_cases j <;> simp at e' ⊢ <;> omega
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
    exact ⟨_, add_comm _ _⟩
  · simp only [HChar.locInf_mul, hν, sign_abs, mul_one]
    exact Units.ext ((sign_hol hφ hne v).trans ((sign_eq k (t v)).trans ((sign_eq k (t v')).symm.trans (sign_hol hφ hne v').symm)))
  · obtain ⟨B, hl, hr, hf, hc, hX⟩ := P.gkR F 2 π
    refine TR.CuspSub.isSelfDualBy_of_iso B hl hr hf hc hX (P.smoR F 2 one_le_two _ _ ?_)
    filter_upwards [GlobalTheory.CuspRep.LocSph.eventually_mem ((π.isSmooth_finPart (T x₀)).mem_nhds
        (show π.finPart 1 (T x₀) = T x₀ by rw [map_one]; rfl)),
      Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified (ω * ν * ν))] with w hw hu
    obtain ⟨α, β, h2, -, h3⟩ := hsat w (by rintro _ ⟨g, rfl⟩; exact hw g)
    have e : (({α, β} : Multiset ℂˣ).map (·⁻¹)).map (· * (ω * ν * ν).val w) = {α, β} := by
      rw [← h3, Multiset.pair_comm α β]
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, inv_mul_cancel_left]
      rw [mul_comm α β, inv_mul_cancel_left]
      exact Multiset.pair_comm α β
    exact ⟨_, h2, e ▸ h2.dual.twist hu⟩
  · obtain ⟨α, β, h2, h3, h4⟩ := hsat w (by have := hfix w; rwa [hw, iwahori_level_zero_eq] at this)
    refine ⟨_, h2, ?_⟩
    have h5 := hU w
    rw [hw] at h5
    have h6 := smul_left_injective ℂ hx0 (h5.symm.trans h3)
    have h7 : (α : ℂ) * β = (ω.val w : ℂˣ) * (ν.val w : ℂˣ) * (ν.val w : ℂˣ) := congrArg Units.val h4
    set r : ℂ := (((normV w : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) with hr
    have h8 : r * r * ((ν.val w : ℂˣ) * (ν.val w : ℂˣ)) = (normV w : ℂ) ^ (k - 1) := by
      rw [hν3, hr, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.rpow_add (hq w),
        ← Real.rpow_add (hq w), ← Real.rpow_add (hq w),
        show (1 / 2 + 1 / 2 + ((k : ℝ) / 2 - 1 + (k / 2 - 1))) = ((k - 1 : ℕ) : ℝ) by
          rw [Nat.cast_sub (by omega)]; push_cast; ring, Real.rpow_natCast]
      simp
    have h9 : algSat 2 (normV w) {α, β} = {r * α, r * β} := by
      simp only [algSat, hr, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
      norm_num
    rw [h9, h6, ← h8, show (ω.val w : ℂˣ) * (r * r * (((ν.val w : ℂˣ) : ℂ) * (ν.val w : ℂˣ))) = r * α * (r * β) by
      linear_combination (-(r * r)) * h7]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
      Multiset.prod_singleton, map_mul, map_add]
    ring
end UpperTheory.Esk.HeckeRepresentationSatake
end
end
end

section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.Esk
theorem mixSeed_of_holWC_alt (w : HolWC) (P : _root_.UpperTheory.V.Af.HypothesesH') (h : UpperTheory.V.Sd.PropMHol) : _root_.UpperTheory.V.Z.Win.Birth.MixSeedP :=
  _root_.UpperTheory.V.Z.Win.Birth.mix_birth_of_prints P (_root_.UpperTheory.Esk.pf_PropMV_sv_alt P h w (_root_.UpperTheory.Esk.pf_HRep_alt P s_HCap))
end UpperTheory.Esk
end
end

section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.Esk
theorem mixSeed_of_alt (P : _root_.UpperTheory.V.Af.HypothesesH') (h : UpperTheory.V.Sd.PropMHol) : _root_.UpperTheory.V.Z.Win.Birth.MixSeedP := _root_.UpperTheory.Esk.mixSeed_of_holWC_alt holWC P h
end UpperTheory.Esk
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
theorem UpperTheory.V.Sd.holomorphic_finite_of_printed_hida :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Sd.HolFin := fun _ => UpperTheory.V.Br.holFin0
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
namespace UpperTheory.V.Sd
variable {F : Type} [Field F] [NumberField F]
private theorem val_pow (ω : HChar F) (w : Pl F) (n : ℕ) : (ω ^ n).val w = ω.val w ^ n := by
  induction n with
  | zero => simp [HChar.val, HChar.locK, HChar.loc]
  | succ n ih => rw [pow_succ, pow_succ, HChar.val_mul, ih]
private theorem norm_chiI {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ω : HChar F) (hω : IsOfFinOrder ω) (c : Pl F → ℕ)
    (I : Ideal (𝓞 F)) : ‖ι.symm (chiI ω c I)‖ ≤ 1 := by
  obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.1 hω
  refine finprod_induction (fun x : ℂ => ‖ι.symm x‖ ≤ 1) (by simp) ?_ ?_
  · intro x y hx hy
    rw [map_mul, norm_mul]
    exact mul_le_one₀ hx (norm_nonneg _) hy
  · intro w
    rw [map_pow, norm_pow]
    refine pow_le_one₀ (norm_nonneg _) ?_
    split_ifs
    · have h1 : (ι.symm ((ω.val w : ℂˣ) : ℂ)) ^ n = 1 := by
        rw [← map_pow, ← Units.val_pow_eq_pow_val, ← val_pow, h, ← pow_zero ω, val_pow]; simp
      have h2 := congrArg norm h1
      rw [norm_pow, norm_one] at h2
      exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2).le
    · simp
private abbrev Idx (F : Type) [Field F] : Type := {𝔪 : Ideal (𝓞 F) // 𝔪 ≠ ⊥}
open Classical in
private def fT {K : Type} [Field K] (w : Pl F) (e : K) : Module.End K (Idx F → K) where
  toFun v 𝔪 := v ⟨w.asIdeal * 𝔪.1, mul_ne_zero w.ne_bot 𝔪.2⟩ +
    e * if h : ∃ 𝔫, 𝔪.1 = w.asIdeal * 𝔫 then
      v ⟨h.choose, fun h0 => 𝔪.2 (by rw [h.choose_spec, h0, Ideal.mul_bot])⟩ else 0
  map_add' c d := by
    funext n
    by_cases h : ∃ 𝔫, n.1 = w.asIdeal * 𝔫 <;> simp only [h, dif_pos, dif_neg, not_false_eq_true, Pi.add_apply] <;> ring
  map_smul' a c := by
    funext n
    by_cases h : ∃ 𝔫, n.1 = w.asIdeal * 𝔫 <;>
      simp only [h, dif_pos, dif_neg, not_false_eq_true, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] <;> ring
open Classical in
omit [NumberField F] in
private theorem fT_apply {K : Type} [Field K] (w : Pl F) (e : K) (v : Idx F → K) (𝔪 : Idx F) :
    fT w e v 𝔪 = v ⟨w.asIdeal * 𝔪.1, mul_ne_zero w.ne_bot 𝔪.2⟩ +
    e * if h : ∃ 𝔫, 𝔪.1 = w.asIdeal * 𝔫 then
      v ⟨h.choose, fun h0 => 𝔪.2 (by rw [h.choose_spec, h0, Ideal.mul_bot])⟩ else 0 := rfl
variable [IsTotallyReal F]
private def SS (k : ℕ) (c : Pl F → ℕ) (ω : HChar F) : Submodule ℂ (TR.Sm F 2) where
  carrier := {φ | IsHol k c ω φ ∧ ∃ c₀ a, HasExp φ.1 k c₀ a}
  zero_mem' := ⟨(holLin F k c ω).1, _, _, (holLin F k c ω).2.1⟩
  add_mem' := by
    rintro φ ψ ⟨h1, c₀, a, h2⟩ ⟨h3, d₀, b, h4⟩
    have e1 := (holLin F k c ω).2.2.1 φ ψ 1 h1 h3
    have e2 := (holLin F k c ω).2.2.2.1 φ.1 ψ.1 1 _ _ _ _ h2 h4
    rw [one_smul] at e1 e2
    exact ⟨e1, _, _, e2⟩
  smul_mem' := by
    rintro z ψ ⟨h3, d₀, b, h4⟩
    have e1 := (holLin F k c ω).2.2.1 0 ψ z (holLin F k c ω).1 h3
    have e2 := (holLin F k c ω).2.2.2.1 0 ψ.1 z _ _ _ _ (holLin F k c ω).2.1 h4
    rw [zero_add] at e1 e2
    exact ⟨e1, _, _, e2⟩
private def cf {k : ℕ} {c : Pl F → ℕ} {ω : HChar F} (φ : SS k c ω) : Ideal (𝓞 F) → ℂ := φ.2.2.choose_spec.choose
private theorem cf_spec {k : ℕ} {c : Pl F → ℕ} {ω : HChar F} (φ : SS k c ω) : ∃ c₀, HasExp φ.1.1 k c₀ (cf φ) :=
  ⟨_, φ.2.2.choose_spec.choose_spec⟩
private theorem cf_eq {k : ℕ} {c : Pl F → ℕ} {ω : HChar F} (φ : SS k c ω) {c₀ a} (h : HasExp φ.1.1 k c₀ a) (𝔪 : Idx F) :
    cf φ 𝔪.1 = a 𝔪.1 := by
  obtain ⟨d, hd⟩ := cf_spec φ
  exact (expUnique F _ k _ _ _ _ hd h).2 _ 𝔪.2
private def Phi {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (k : ℕ) (c : Pl F → ℕ) (ω : HChar F) :
    SS k c ω →ₛₗ[(ι.symm : ℂ →+* Qbar l)] (Idx F → Qbar l) where
  toFun φ 𝔪 := ι.symm (cf φ 𝔪.1)
  map_add' φ ψ := by
    funext 𝔪
    obtain ⟨_, h2⟩ := cf_spec φ
    obtain ⟨_, h4⟩ := cf_spec ψ
    have e2 := (holLin F k c ω).2.2.2.1 _ _ 1 _ _ _ _ h2 h4
    simp only [one_smul] at e2
    rw [cf_eq (φ + ψ) e2]
    simp
  map_smul' z ψ := by
    funext 𝔪
    obtain ⟨_, h4⟩ := cf_spec ψ
    have e2 := (holLin F k c ω).2.2.2.1 0 _ z _ _ _ _ (holLin F k c ω).2.1 h4
    simp only [zero_add] at e2
    rw [cf_eq (z • ψ) e2]
    simp
private theorem Phi_eq {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {k : ℕ} {c : Pl F → ℕ} {ω : HChar F} (φ : SS k c ω) {c₀ a}
    (h : HasExp φ.1.1 k c₀ a) (𝔪 : Idx F) : Phi ι k c ω φ 𝔪 = ι.symm (a 𝔪.1) := congrArg ι.symm (cf_eq φ h 𝔪)
private theorem fT_Phi {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {k : ℕ} {c : Pl F → ℕ} {ω : HChar F} (φ : SS k c ω) {c₀ a}
    (h : HasExp φ.1.1 k c₀ a) (w : Pl F) (𝔪 : Idx F) :
    fT w (ι.symm (chiI ω c w.asIdeal * (normV w : ℂ) ^ (k - 1))) (Phi ι k c ω φ) 𝔪 = ι.symm (hkCoef k c ω w a 𝔪.1) := by
  rw [fT_apply, Phi_eq ι φ h, hkCoef, map_add, map_mul ι.symm _ (coefDiv _ _ _), coefDiv]
  split_ifs with hd
  · rw [Phi_eq ι φ h]
  · rw [map_zero]
private def hkS {k : ℕ} (hk1 : 1 ≤ k) (c : Pl F → ℕ) {ω : HChar F} (hω : IsOfFinOrder ω) (w : Pl F) (φ : SS k c ω) : SS k c ω :=
  ⟨hk k w (c w) φ.1, (holHk F k hk1 c ω hω φ.1 φ.2.1 w).1, by
    obtain ⟨_, h⟩ := cf_spec φ
    obtain ⟨d, hd⟩ := (holHk F k hk1 c ω hω φ.1 φ.2.1 w).2.2 _ _ h
    exact ⟨d, _, hd⟩⟩
private theorem Phi_hkS {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {k : ℕ} (hk1 : 1 ≤ k) (c : Pl F → ℕ) {ω : HChar F}
    (hω : IsOfFinOrder ω) (w : Pl F) (φ : SS k c ω) :
    fT w (ι.symm (chiI ω c w.asIdeal * (normV w : ℂ) ^ (k - 1))) (Phi ι k c ω φ) = Phi ι k c ω (hkS hk1 c hω w φ) := by
  funext 𝔪
  obtain ⟨_, h⟩ := cf_spec φ
  obtain ⟨d, hd⟩ := (holHk F k hk1 c ω hω φ.1 φ.2.1 w).2.2 _ _ h
  rw [fT_Phi ι φ h, Phi_eq ι (hkS hk1 c hω w φ) hd]
private theorem Phi_inj {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {k : ℕ} (hk1 : 1 ≤ k) (c : Pl F → ℕ) {ω : HChar F}
    (hω : IsOfFinOrder ω) : Function.Injective (Phi ι k c ω) := by
  rw [injective_iff_map_eq_zero]
  intro φ h0
  obtain ⟨_, h⟩ := cf_spec φ
  refine Subtype.ext (expInj F k hk1 c ω hω φ.1 φ.2.1 _ _ h fun 𝔪 h𝔪 => ?_)
  have := congrFun h0 ⟨𝔪, h𝔪⟩
  rw [Phi_eq ι φ h] at this
  simpa using this
end UpperTheory.V.Sd
open UpperTheory.V.Sd in
theorem UpperTheory.V.Sd.holLift_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Sd.HolLift := by
  intro hP F _ _ _ l _ ι k hk1 c hc ω hω φ c₀ a t hφ hexp hint h1 ht hcong
  haveI : RingHomSurjective (ι.symm : ℂ →+* Qbar l) := ⟨ι.symm.surjective⟩
  haveI := _root_.UpperTheory.V.Sd.holomorphic_finite_of_printed_hida hP F k c hc ω hω
  haveI : FiniteDimensional ℂ (SS k c ω) :=
    Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {φ : TR.Sm F 2 | IsHol k c ω φ})
      fun ψ hψ => Submodule.subset_span hψ.1
  set V : Submodule (Qbar l) (Idx F → Qbar l) := (⊤ : Submodule ℂ (SS k c ω)).map (Phi ι k c ω) with hV
  have hfd : FiniteDimensional (Qbar l) V :=
    Module.Finite.iff_fg.2 (Submodule.FG.map _ (IsNoetherian.noetherian _))
  let e : Pl F → Qbar l := fun w => ι.symm (chiI ω c w.asIdeal * (normV w : ℂ) ^ (k - 1))
  have he : ∀ p, ‖e p‖ ≤ 1 := by
    intro p
    simp only [e, map_mul, map_pow, map_natCast, norm_mul, norm_pow]
    exact mul_le_one₀ (norm_chiI ι ω hω c _) (by positivity)
      (pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _))
  have hmem : ∀ p : Pl F, ∀ v ∈ V, fT p (e p) v ∈ V := by
    rintro p _ ⟨g, -, rfl⟩
    exact ⟨hkS hk1 c hω p g, trivial, (Phi_hkS ι hk1 c hω p g).symm⟩
  let T : Pl F → Module.End (Qbar l) V := fun p => (fT p (e p)).restrict (hmem p)
  have hT : ∀ p (v : V), (T p v).1 = fT p (e p) v.1 := fun _ _ => rfl
  let f : SS k c ω := ⟨φ, hφ, _, _, hexp⟩
  obtain ⟨h, b, hne, -, heig, hb⟩ := delSerre l (Idx F) (Pl F) V hfd T
    (by
      intro p q
      ext1 v
      apply Subtype.ext
      obtain ⟨_, g, -, rfl⟩ := v
      simp only [Module.End.mul_apply, hT, e, Phi_hkS ι hk1 c hω]
      exact congrArg _ (Subtype.ext ((holHk F k hk1 c ω hω g.1 g.2.1 p).2.1 q)))
    (by
      intro p v hv n
      rw [hT, fT_apply]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hv _) ?_)
      rw [norm_mul]
      refine mul_le_one₀ (he p) (norm_nonneg _) ?_
      split_ifs
      · exact hv _
      · simp)
    (by
      intro p v hv n
      rw [hT, fT_apply]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hv _) ?_)
      rw [norm_mul]
      refine (mul_le_of_le_one_left (norm_nonneg _) (he p)).trans_lt ?_
      split_ifs
      · exact hv _
      · simp)
    ⟨Phi ι k c ω f, f, trivial, rfl⟩ (fun p => ι.symm (t p))
    (by
      intro n
      show ‖Phi ι k c ω f n‖ ≤ 1
      rw [Phi_eq ι f hexp]
      exact hint _ n.2)
    ⟨⟨⊤, top_ne_bot⟩, by
      show ‖Phi ι k c ω f _‖ = 1
      rw [Phi_eq ι f hexp]; exact h1⟩
    ht
    (by
      intro p n
      rw [hT]
      show ‖fT p (e p) (Phi ι k c ω f) n - ι.symm (t p) * Phi ι k c ω f n‖ < 1
      rw [fT_Phi ι f hexp, Phi_eq ι f hexp, ← map_mul, ← map_sub]
      exact hcong p _ n.2)
  obtain ⟨_, g, hg, rfl⟩ := h
  refine ⟨g.1, fun w => ι (b w), ⟨g.2.1, fun h0 => hne ?_, fun w => ?_⟩, fun w => ?_⟩
  · apply Subtype.ext
    show Phi ι k c ω g = 0
    rw [show g = 0 from Subtype.ext h0, map_zero]
  · have h2 : fT w (e w) (Phi ι k c ω g) = b w • Phi ι k c ω g := congrArg Subtype.val (heig w)
    have h3 : hkS hk1 c hω w g = ι (b w) • g := by
      apply Phi_inj ι hk1 c hω
      rw [← Phi_hkS, LinearMap.map_smulₛₗ]
      refine h2.trans ?_
      simp
    exact congrArg Subtype.val h3
  · rw [map_sub, RingEquiv.symm_apply_apply]
    exact hb w
end
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
  GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Base UpperTheory.V.Sd
section SlopeTestRemainingChoices
variable {l : ℕ} [Fact l.Prime]
private theorem sm_add {x y : Qbar l} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x + y‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max x y).trans_lt (max_lt hx hy)
private theorem sm_sub {x y : Qbar l} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x - y‖ < 1 := by
  rw [sub_eq_add_neg]; exact sm_add hx (by rwa [norm_neg])
private theorem sm_mul {x y : Qbar l} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ < 1) : ‖x * y‖ < 1 := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans_lt hy
private theorem le_of_cong {x y : Qbar l} (h : ‖x - y‖ < 1) (hy : ‖y‖ ≤ 1) : ‖x‖ ≤ 1 := by
  have := IsUltrametricDist.norm_add_le_max (x - y) y
  rw [sub_add_cancel] at this
  exact this.trans (max_le h.le hy)
private theorem eq_of_cong {x y : Qbar l} (h : ‖x - y‖ < 1) (hy : ‖y‖ = 1) : ‖x‖ = 1 := by
  refine le_antisymm (le_of_cong h hy.le) (not_lt.1 fun hx => ?_)
  have := sm_sub hx h
  rw [sub_sub_cancel, hy] at this
  exact lt_irrefl _ this
private theorem inv_cong {x : Qbar l} (h : ‖x⁻¹ - 1‖ < 1) : ‖x - 1‖ < 1 := by
  have h1 := eq_of_cong h norm_one
  rw [norm_inv, inv_eq_one] at h1
  have h0 : x ≠ 0 := by rintro rfl; simp at h1
  have := sm_mul h1.le h
  rw [mul_sub, mul_inv_cancel₀ h0, mul_one, norm_sub_rev] at this
  exact this
private theorem norm_nat_lt {n : ℕ} (h : l ∣ n) : ‖(n : Qbar l)‖ < 1 := by
  obtain ⟨m, rfl⟩ := h
  rw [Nat.cast_mul, mul_comm]
  refine sm_mul (IsUltrametricDist.norm_natCast_le_one _ _) ?_
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one
private theorem pow_cong {n k : ℕ} (h : ¬ l ∣ n) (hk : l - 1 ∣ k) : ‖(n : Qbar l) ^ k - 1‖ < 1 := by
  obtain ⟨m, rfl⟩ := hk
  have hp : l.Prime := Fact.out
  have h1 : n ^ (l - 1) ≡ 1 [MOD l] := by
    rw [← Nat.totient_prime hp]
    exact Nat.ModEq.pow_totient ((Nat.Prime.coprime_iff_not_dvd hp).2 h).symm
  have h2 : n ^ ((l - 1) * m) ≡ 1 [MOD l] := by
    rw [pow_mul]; simpa using h1.pow m
  have h0 : 1 ≤ n ^ ((l - 1) * m) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (by rintro rfl; simp at h))
  have := norm_nat_lt ((Nat.modEq_iff_dvd' h0).1 h2.symm)
  rwa [Nat.cast_sub h0, Nat.cast_pow, Nat.cast_one] at this
variable {F : Type} [Field F] [NumberField F]
private theorem dvd_normV (w : Pl F) : l ∣ normV w ↔ ((l : ℕ) : 𝓞 F) ∈ w.asIdeal := by
  have := w.isMaximal
  letI := Ideal.Quotient.field w.asIdeal
  have : Finite (𝓞 F ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  letI := Fintype.ofFinite (𝓞 F ⧸ w.asIdeal)
  rw [normV, Nat.card_eq_fintype_card, ← prime_dvd_char_iff_dvd_card, ← Ideal.Quotient.eq_zero_iff_mem, map_natCast,
    ringChar.spec]
  have hq : (ringChar (𝓞 F ⧸ w.asIdeal)).Prime := CharP.prime_ringChar _
  rw [Nat.prime_dvd_prime_iff_eq Fact.out hq, Nat.prime_dvd_prime_iff_eq hq Fact.out, eq_comm]
private theorem norm_val (ι : Qbar l ≃+* ℂ) {η : HChar F} (h : IsOfFinOrder η) (x : Ideles F) :
    ‖ι.symm (η.1 x : ℂˣ)‖ = 1 := by
  obtain ⟨m, hm, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have e1 : η.1 x ^ m = 1 := DFunLike.congr_fun (congrArg Subtype.val e) x
  have e2 : ‖ι.symm (η.1 x : ℂˣ)‖ ^ m = 1 := by
    rw [← norm_pow, ← map_pow, ← Units.val_pow_eq_pow_val, e1, Units.val_one, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 e2
private theorem chiI_prime (ω : HChar F) (c : Pl F → ℕ) (w : Pl F) :
    chiI ω c w.asIdeal = if c w = 0 then ((ω.val w : ℂˣ) : ℂ) else 0 := by
  classical
  rw [chiI, finprod_eq_single _ w]
  · rw [ordI, Associates.count_self w.associates_irreducible, pow_one]
  · intro v hv
    rw [ordI, Associates.count_eq_zero_of_ne v.associates_irreducible w.associates_irreducible, pow_zero]
    intro e
    exact hv (HeightOneSpectrum.ext (associated_iff_eq.1 (Associates.mk_eq_mk_iff_associated.1 e)))
private theorem gal_of (hA : GlobalTheory.Published.GlobalArtinReciprocity) (ι : Qbar l ≃+* ℂ) {η₁ η₂ : HChar F} (h₁ : IsOfFinOrder η₁)
    (h₂ : IsOfFinOrder η₂) {S : Set (Pl F)} (hS : S.Finite)
    (h : ∀ w ∉ S, η₁.UnrAt w ∧ η₂.UnrAt w ∧ (‖ι.symm (η₁.val w : ℂˣ) - 1‖ < 1 ∨ ‖ι.symm (η₂.val w : ℂˣ) - 1‖ < 1))
    (x : Ideles F) : ‖ι.symm (η₁.1 x : ℂˣ) - 1‖ < 1 ∨ ‖ι.symm (η₂.1 x : ℂˣ) - 1‖ < 1 := by
  obtain ⟨art, ha⟩ := hA F (AlgebraicClosure F)
  obtain ⟨m₁, hm₁, e₁⟩ := isOfFinOrder_iff_pow_eq_one.1 h₁
  obtain ⟨m₂, hm₂, e₂⟩ := isOfFinOrder_iff_pow_eq_one.1 h₂
  obtain ⟨δ₁, c₁, L₁⟩ := ha.exists_isLAdicOf ι (isAlgPos_zero_of_orderDvd (χ := η₁) hm₁ e₁)
  obtain ⟨δ₂, c₂, L₂⟩ := ha.exists_isLAdicOf ι (isAlgPos_zero_of_orderDvd (χ := η₂) hm₂ e₂)
  have hcl : IsClosed ((fun σ => (δ₁ σ : Qbar l)) ⁻¹' Metric.ball 1 1 ∪ (fun σ => (δ₂ σ : Qbar l)) ⁻¹' Metric.ball 1 1) :=
    ((IsUltrametricDist.isClosed_ball _ _).preimage (Units.continuous_val.comp c₁)).union
      ((IsUltrametricDist.isClosed_ball _ _).preimage (Units.continuous_val.comp c₂))
  obtain ⟨σ, hσ⟩ := toAb_surjective (art x)
  have hd := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := F) (Ω := AlgebraicClosure F) GlobalTheory.Published.chebotarevDegreeOne' hS
  have hm := hcl.closure_subset_iff.2 ?_ (hd σ)
  · have f₁ := L₁ x σ hσ.symm
    have f₂ := L₂ x σ hσ.symm
    rw [infPow_zero, lPow_zero, inv_one, mul_one, mul_one] at f₁ f₂
    simpa only [Set.mem_union, Set.mem_preimage, mem_ball_iff_norm, f₁, f₂] using hm
  · rintro τ ⟨v, hv, -, B, hB, hτ⟩
    obtain ⟨u₁, u₂, hh⟩ := h v hv
    simp only [Set.mem_union, Set.mem_preimage, mem_ball_iff_norm, L₁.frob_unr ha (Or.inr rfl) u₁ hB hτ,
      L₂.frob_unr ha (Or.inr rfl) u₂ hB hτ]
    exact hh.imp (fun t => inv_cong (by rwa [inv_inv])) fun t => inv_cong (by rwa [inv_inv])
end SlopeTestRemainingChoices
theorem UpperTheory.V.Z.Bc.propMHolZ_alt :
    _root_.UpperTheory.V.Z.Bc.Hypotheses4Z' → UpperTheory.V.Sd.PropMHol := by
  intro PP F _ _ _ l _ hl ι ω c hω hodd hc hne hcl P hP hQ B
  have hp : l.Prime := Fact.out
  obtain ⟨v, hvP, hvl, hv⟩ := hP
  obtain ⟨v', hvQ, hvl', hv'⟩ := hQ
  obtain ⟨φ, a, hφ, eφ, a1, aint, aeig⟩ := emix PP.eis F l ι ω c hω hodd hc hne hcl P ⟨v, hvP, hvl⟩
  have hl1 : 0 < l - 1 := Nat.sub_pos_of_lt hp.one_lt
  obtain ⟨k, hkB, hk0, hkd', ψ, d₀, b, hψ, eψ, hd, hb⟩ := PP.one F l hl ι B
  obtain ⟨χ, a', hχ, eχ, ha'⟩ := holMul F l ι 1 k (levL l c) ω hω φ ψ a d₀ b hφ hψ eφ eψ aint hd hb
  rw [add_comm 1 k] at hχ eχ
  simp only [map_sub] at ha'
  have hfin : {w | levL l c w ≠ 0}.Finite := by
    have h0 : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ 0 := by
      simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero
    refine ((Ideal.finite_factors h0).union (GlobalTheory.Mem.UnrAe.unr_ae_and_level F ω).1).subset fun w hw => ?_
    by_cases h : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal
    · exact Or.inl (Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 h))
    · refine Or.inr fun hu => hw ?_
      rw [levL, if_neg h]
      exact Nat.le_zero.1 ((hc w).2 fun x hx _ => hu x hx)
  have hL0 : ∀ w, levL l c w = 0 → ((l : ℕ) : 𝓞 F) ∉ w.asIdeal ∧ c w = 0 := fun w hw => by
    by_cases h : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal
    · rw [levL, if_pos h] at hw; exact absurd hw one_ne_zero
    · rw [levL, if_neg h] at hw; exact ⟨h, hw⟩
  have nval : ∀ {η : HChar F}, IsOfFinOrder η → ∀ w, ‖ι.symm (η.val w : ℂˣ)‖ = 1 := fun h w => norm_val ι h _
  have hpow : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ‖(normV w : Qbar l) ^ k - 1‖ < 1 := fun w hw =>
    pow_cong (mt (dvd_normV w).1 hw) hkd'
  have ht : ∀ w, ‖ι.symm (eisT l ω c P w)‖ ≤ 1 := fun w => by
    rw [eisT]
    split_ifs
    · exact (nval hω w).le
    · simp
    · rw [map_add, map_one]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le norm_one.le (nval hω w).le)
    · simp
  obtain ⟨g, lam, hg, hlam⟩ := _root_.UpperTheory.V.Sd.holLift_alt PP.h F l ι (k + 1) (Nat.le_add_left _ _) (levL l c) hfin ω hω χ 0 a'
    (eisT l ω c P) hχ eχ (fun 𝔪 h => le_of_cong (ha' 𝔪 h) (aint 𝔪 h))
    (eq_of_cong (ha' ⊤ top_ne_bot) (by rw [a1, map_one, norm_one])) ht (fun w 𝔪 h𝔪 => by
      have e := aeig w 𝔪 h𝔪
      have h1 := ha' _ (mul_ne_zero w.ne_bot h𝔪)
      have h2 := sm_mul (ht w) (ha' 𝔪 h𝔪)
      have h3 : ‖ι.symm (coefDiv a w.asIdeal 𝔪)‖ ≤ 1 ∧
          ‖ι.symm (coefDiv a' w.asIdeal 𝔪) - ι.symm (coefDiv a w.asIdeal 𝔪)‖ < 1 := by
        unfold coefDiv
        split_ifs with h
        · have h0 : h.choose ≠ ⊥ := fun h0 => h𝔪 (by rw [h.choose_spec, h0, Ideal.mul_bot])
          exact ⟨aint _ h0, ha' _ h0⟩
        · simp
      rw [hkCoef, chiI_prime, Nat.sub_self, pow_zero, mul_one] at e
      have e' := congrArg ι.symm e
      rw [hkCoef, chiI_prime, Nat.add_sub_cancel]
      split_ifs at e' ⊢ with h0
      · have h4 := sm_mul (nval hω w).le (sm_add (sm_mul (le_of_cong (hpow w (hL0 w h0).1) norm_one.le) h3.2)
          (sm_mul h3.1 (hpow w (hL0 w h0).1)))
        convert sm_add (sm_sub h1 h2) h4 using 2
        simp only [map_add, map_sub, map_mul, map_pow, map_natCast] at e' ⊢
        linear_combination e'
      · convert sm_sub h1 h2 using 2
        simp only [map_add, map_sub, map_mul, map_pow, map_natCast, map_zero] at e' ⊢
        linear_combination e')
  refine ⟨k, hkB, hkd', g, lam, hg, ?_, hlam⟩
  by_contra hcusp
  obtain ⟨η₁, η₂, f₁, f₂, rfl, hu, hr⟩ := holEis F (k + 1) (Nat.le_add_left _ _) (levL l c) hfin ω hω g lam hg hcusp
  simp only [map_sub, Nat.add_sub_cancel] at hlam hu hr
  have key := gal_of PP.h.litN.aut.art ι f₁ f₂ hfin fun w hw => by
    have h0 : levL l c w = 0 := not_not.1 hw
    obtain ⟨u₁, u₂, e⟩ := hu w h0
    refine ⟨u₁, u₂, ?_⟩
    have h1 := hlam w
    rw [e, eisT, if_neg (hL0 w h0).1, if_pos (hL0 w h0).2, HChar.val_mul] at h1
    have h2 := sm_sub (sm_mul (nval f₂ w).le (hpow w (hL0 w h0).1)) h1
    have h3 : ‖ι.symm (η₁.val w : ℂˣ) - 1‖ * ‖ι.symm (η₂.val w : ℂˣ) - 1‖ < 1 := by
      rw [← norm_mul]
      convert h2 using 2
      simp only [map_add, map_mul, map_pow, map_natCast, map_one, Units.val_mul]
      ring
    by_contra hn
    rw [not_or, not_lt, not_lt] at hn
    exact h3.not_ge (one_le_mul_of_one_le_of_one_le hn.1 hn.2)
  have hab : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ‖ι.symm (eisT l (η₁ * η₂) c P w)‖ = 1 →
      ‖ι.symm (η₁.val w : ℂˣ) - ι.symm (eisT l (η₁ * η₂) c P w)‖ < 1 := fun w hw h1 => by
    have h2 := eq_of_cong (hlam w) h1
    rcases hr w (fun h0 => (hL0 w h0).1 hw) with e | ⟨-, e⟩ | ⟨-, e⟩
    · simp [e] at h2
    · exact e ▸ hlam w
    · rw [e, map_mul, map_pow, map_natCast, ← Nat.cast_pow] at h2
      exact absurd h2 (sm_mul (nval f₂ w).le (norm_nat_lt (dvd_pow ((dvd_normV w).2 hw) hk0.ne'))).ne
  have e₁ : eisT l (η₁ * η₂) c P v = ((η₁ * η₂).val v : ℂˣ) := by rw [eisT, if_pos hvl, if_pos hvP]
  have e₂ : eisT l (η₁ * η₂) c P v' = 1 := by rw [eisT, if_pos hvl', if_neg hvQ]
  have a₁ := hab v hvl (by rw [e₁]; exact nval hω v)
  have a₂ := hab v' hvl' (by rw [e₂, map_one, norm_one])
  rw [e₁] at a₁
  rw [e₂, map_one] at a₂
  have kk : ‖ι.symm (η₁.val v * η₁.val v' : ℂˣ) - 1‖ < 1 ∨ ‖ι.symm (η₂.val v * η₂.val v' : ℂˣ) - 1‖ < 1 := by
    have := key (localIdele F v (atFin v (unif v)) * localIdele F v' (atFin v' (unif v')))
    rw [map_mul η₁.1, map_mul η₂.1] at this
    exact this
  simp only [HChar.val_mul, Units.val_mul, map_mul] at kk a₁ hv hv'
  have n₁ := nval f₁ v
  have n₂ := nval f₂ v
  have n₃ := nval f₁ v'
  have n₄ := nval f₂ v'
  generalize ι.symm (η₁.val v : ℂˣ) = x at *
  generalize ι.symm (η₂.val v : ℂˣ) = y at *
  generalize ι.symm (η₁.val v' : ℂˣ) = x' at *
  generalize ι.symm (η₂.val v' : ℂˣ) = y' at *
  have hy : ‖y - 1‖ < 1 := by
    rwa [← mul_one_sub, norm_mul, n₁, one_mul, norm_sub_rev] at a₁
  rcases kk with h | h
  · refine hv ?_
    convert sm_sub (sm_sub h (sm_mul n₁.le a₂)) a₁ using 2
    ring
  · refine hv' ?_
    convert sm_add (sm_sub h (sm_mul n₄.le hy)) (sm_mul n₄.le a₂) using 2
    ring
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2
namespace UpperTheory.V.Z.Bc
theorem seedII_Z_alt (h : _root_.UpperTheory.V.Z.Bc.Hypotheses4Z') (hI : _root_.UpperTheory.V.Z.Win.Birth.IndAutLP) : _root_.UpperTheory.V.Ws.SeedIIAlt :=
  _root_.UpperTheory.V.Z.Bc.seedII_of_p_alt (_root_.UpperTheory.V.Z.Win.Birth.mixOfP (_root_.UpperTheory.Esk.mixSeed_of_alt h.h (_root_.UpperTheory.V.Z.Bc.propMHolZ_alt h))) hI
end UpperTheory.V.Z.Bc
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Ws UpperTheory.V.Base UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E
open scoped Matrix
private theorem alg_closure_of (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (k₀ : IntermediateField ℚ Ω) :
    IsAlgClosure k₀ Ω :=
  ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) k₀⟩
private theorem conj_el_ex (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (k₀ : IntermediateField ℚ Ω) [NumberField k₀]
    [IsTotallyReal k₀] : ∃ c : G k₀ Ω, IsConjEl c := by
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  let j : Ω →ₐ[ℚ] ℂ := IsAlgClosed.lift
  letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  let τ : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := starRingAut) fun x => by simp
  let c : Ω ≃ₐ[ℚ] Ω := τ.restrictNormal Ω
  have hc : ∀ x, algebraMap Ω ℂ (c x) = starRingEnd ℂ (algebraMap Ω ℂ x) := fun x => AlgEquiv.restrictNormal_commutes τ Ω x
  have hfix : ∀ y : k₀, c (y : Ω) = y := fun y => by
    apply (algebraMap Ω ℂ).injective
    rw [hc]
    let φ : k₀ →+* ℂ := (algebraMap Ω ℂ).comp (algebraMap k₀ Ω)
    have hr : ComplexEmbedding.IsReal φ :=
      InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal (InfinitePlace.mk φ))
    exact RingHom.congr_fun (ComplexEmbedding.isReal_iff.1 hr) y
  refine ⟨AlgEquiv.ofRingEquiv (f := c.toRingEquiv) fun y => hfix y, algebraMap Ω ℂ, fun x => hc x⟩
private theorem pair_two {k : Type} [Field k] (A : Matrix (Fin 2) (Fin 2) k) :
    Aᵀ * !![0, 1; -1, 0] * A = A.det • (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) k) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.det_fin_two] <;> ring
private theorem pairing_two {F Ω k : Type} [Field F] [Field Ω] [Algebra F Ω] [Field k] (r : G F Ω →* GL (Fin 2) k) (c : G F Ω) :
    ∃ P, IsPairing c r ((Matrix.GeneralLinearGroup.det.comp r).comp (resG F F Ω)) P := by
  let J : GL (Fin 2) k := Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp [Matrix.det_fin_two])
  refine ⟨J * r c⁻¹, fun s s' h => ?_⟩
  have h' : s' = c * s * c⁻¹ := h
  have e : r c⁻¹ * r s' = r s * r c⁻¹ := by rw [h', ← map_mul, ← map_mul]; congr 1; group
  have e' : (r c⁻¹).val * (r s').val = (r s).val * (r c⁻¹).val := congrArg Units.val e
  have hp : (r s).valᵀ * J.val * (r s).val = (r s).val.det • J.val := pair_two _
  have hd : (((Matrix.GeneralLinearGroup.det.comp r).comp (resG F F Ω) s : kˣ) : k) = (r s).val.det := rfl
  rw [hd, Units.val_mul, ← Matrix.smul_mul, ← hp]
  simp only [Matrix.mul_assoc, e']
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.polMix_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.PolMix := by
  intro H Ω _ _ _ l _ k₀ _ _ ι x k t r hd hm
  obtain ⟨m, hm0, hm⟩ := hm
  haveI : IsAlgClosure k₀ Ω := alg_closure_of Ω k₀
  have hdet : ∀ s, Matrix.GeneralLinearGroup.det (r s) = cycBar k₀ Ω l s ^ k * x (resQ k₀ s) := fun s =>
    DFunLike.congr_fun hd.det s
  have hcont : Continuous (Matrix.GeneralLinearGroup.det.comp r) :=
    Matrix.GeneralLinearGroup.continuous_det.comp hd.cont
  have halg : Af.IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp r) := by
    refine (_root_.UpperTheory.V.Af.algOfCyc_s H k₀ Ω l ι).1 _ hcont fun w _ => ?_
    obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
    refine ⟨A, hA, k, m, hm0, fun s _ => ?_⟩
    have hx : x (resQ k₀ s) ^ m = 1 := by
      have := DFunLike.congr_fun hm (resQ k₀ s)
      simpa using this
    rw [MonoidHom.comp_apply, hdet, zpow_neg, zpow_natCast, mul_comm (cycBar k₀ Ω l s ^ k), mul_inv_cancel_right, hx]
  have hsign : Sol.SameSign (Matrix.GeneralLinearGroup.det.comp r) := by
    intro c c' hc hc'
    have hres : ∀ {a : G k₀ Ω}, IsConjEl a → IsConjEl (resQ k₀ a) := fun ⟨j, hj⟩ => ⟨j, hj⟩
    have hcj : IsConj (resQ k₀ c) (resQ k₀ c') := UpperTheory.complex_conjugations_are_conjugate Ω _ _ (hres hc) (hres hc')
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hdet, hdet, UpperTheory.cyclotomic_char_conj_invariant k₀ Ω l c hc, UpperTheory.cyclotomic_char_conj_invariant k₀ Ω l c' hc',
      isConj_iff_eq.1 (MonoidHom.map_isConj x hcj)]
  obtain ⟨c, hc⟩ := conj_el_ex Ω k₀
  obtain ⟨P, hP⟩ := pairing_two r c
  exact ⟨k₀, _, _, _, _, inferInstance, inferInstance, inferInstance, _, c, P, halg, hsign, hc, hP⟩
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V UpperTheory.V.Z.Win.Birth
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published UpperTheory.V.Sd UpperTheory.V.Ws UpperTheory.V.Z.Bc UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E
private theorem deg_two {Ω : Type} [Field Ω] [CharZero Ω] (A B M : IntermediateField ℚ Ω) [FiniteDimensional ℚ A]
    [FiniteDimensional ℚ B] (hM : M = A ⊔ B) (hA : Module.finrank ℚ A = 2) (hn : ¬ A ≤ B) [Algebra B M] [IsScalarTower ℚ B M] :
    Module.finrank B M = 2 := by
  have h1 : Module.finrank ℚ M ≤ Module.finrank ℚ A * Module.finrank ℚ B := hM ▸ IntermediateField.finrank_sup_le A B
  haveI : FiniteDimensional ℚ M := hM ▸ IntermediateField.finiteDimensional_sup A B
  haveI : Module.Free B M := Module.Free.of_divisionRing B M
  have h2 := Module.finrank_mul_finrank ℚ B M
  have h3 : 0 < Module.finrank ℚ B := Module.finrank_pos
  have h4 : 0 < Module.finrank ℚ M := Module.finrank_pos
  have h5 : Module.finrank ℚ B ≠ Module.finrank ℚ M := fun e =>
    hn (IntermediateField.eq_of_le_of_finrank_eq (hM ▸ le_sup_right : B ≤ M) e ▸ (hM ▸ le_sup_left : A ≤ M))
  generalize Module.finrank B M = n at h2 ⊢
  rw [hA, ← h2, mul_comm 2] at h1
  have h6 := Nat.le_of_mul_le_mul_left h1 h3
  rw [← h2] at h4 h5
  interval_cases n <;> simp_all
private theorem two_places {k : Type} [Field k] [NumberField k] [IsTotallyReal k] (h : Module.finrank ℚ k = 2)
    {v v' : InfinitePlace k} (hv : v ≠ v') (w : InfinitePlace k) : w = v ∨ w = v' := by
  classical
  by_contra hw
  push Not at hw
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank k
  have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces k
  have h3 : ({w, v, v'} : Finset (InfinitePlace k)).card = 3 := Finset.card_eq_three.2 ⟨w, v, v', hw.1, hw.2, hv, rfl⟩
  have h4 := Finset.card_le_univ ({w, v, v'} : Finset (InfinitePlace k))
  omega
private theorem two_emb {L M : Type} [Field L] [Field M] [CharZero L] [Algebra L M] (h : Module.finrank L M = 2) (φ : L →+* ℂ) :
    ∃ τ τ' : M →+* ℂ, τ ≠ τ' ∧ τ.comp (algebraMap L M) = φ ∧ τ'.comp (algebraMap L M) = φ := by
  letI : Algebra L ℂ := φ.toAlgebra
  haveI : FiniteDimensional L M := Module.finite_of_finrank_pos (by omega)
  have hc := AlgHom.card L M ℂ
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (α := M →ₐ[L] ℂ) (by omega)
  exact ⟨a, b, fun e => hab (AlgHom.coe_ringHom_injective e), a.comp_algebraMap, b.comp_algebraMap⟩
private theorem hom_ext_sup {Ω : Type} [Field Ω] [CharZero Ω] (A B M : IntermediateField ℚ Ω) (hA : A ≤ M) (hB : B ≤ M)
    (hM : M ≤ A ⊔ B) (τ τ' : M →+* ℂ) (eA : ∀ x : A, τ ⟨x, hA x.2⟩ = τ' ⟨x, hA x.2⟩) (eB : ∀ x : B, τ ⟨x, hB x.2⟩ = τ' ⟨x, hB x.2⟩) :
    τ = τ' := by
  let S : IntermediateField ℚ M := (τ.eqLocusField τ').toIntermediateField fun q => by
    rw [RingHom.mem_eqLocusField]
    simp
  have h : M ≤ IntermediateField.lift S := hM.trans <| sup_le
    (fun x hx => (IntermediateField.mem_lift (⟨x, hA hx⟩ : M)).2 (eA ⟨x, hx⟩))
    (fun x hx => (IntermediateField.mem_lift (⟨x, hB hx⟩ : M)).2 (eB ⟨x, hx⟩))
  ext x
  exact (IntermediateField.mem_lift x).1 (h x.2)
private theorem inf_reg (m : Fin 2 → ℤ) (h : m 0 ≠ m 1) :
    (infOf m).Nodup ∧ ∀ z ∈ infOf m, ∃ n : ℤ, z = (n : ℂ) + (((2 : ℕ) : ℂ) - 1) / 2 := by
  refine ⟨Multiset.Nodup.map (fun i j e => ?_) Finset.univ.nodup, fun z hz => ?_⟩
  · have e' : m i = m j := by exact_mod_cast add_left_cancel e
    fin_cases i <;> fin_cases j <;> simp_all
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
    exact ⟨m i, add_comm _ _⟩
private theorem val_of_mem {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v) (p : ℕ) : A.valuation (p : Ω) < 1 ↔ ((p : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  rw [← hA]
  simp
set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.indAutLP_of_upQuad_upSol_indAutCs (H : _root_.UpperTheory.V.Af.HypothesesH') : UpQuadI → UpSolI → IndAutCs → IndAutLP := by
  intro hQ hS hI Ω _ _ _ l _ c D T k₀ _ _ φ ι k t r α β R δ h hrw
  have hKL : T.K ≤ T.L := T.hL ▸ le_sup_right
  have hfix : ∀ g : G T.F Ω, g ∈ T.GalL → resQ T.F g ∈ T.L.fixingSubgroup := fun g hg => by
    rw [T.hL, IntermediateField.fixingSubgroup_sup]
    exact ⟨(IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => g.commutes ⟨y, hy⟩, hg⟩
  have hirr : IsIrr ((R.comp (resQ T.F)).comp T.G'.subtype) := UpperTheory.induced_irreducible Ω l c D T k₀ φ ι k t r α β R δ h
  have hL : IsIrr (R.comp (resQ T.L)) := by
    obtain ⟨h1, -, h3⟩ := hirr
    refine ⟨h1, fun _ _ _ => Submodule.mem_top, fun W hW hi => h3 W hW fun g v hv => ?_⟩
    have hg : resQ T.F g ∈ galOf ℚ T.L Ω := fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hfix g g.2.1) x x.2
    rw [← range_galEmb] at hg
    obtain ⟨g', hg'⟩ := hg
    have := hi g' v hv
    rwa [show (R.comp (resQ T.L)) g' = R (resQ T.F g) from congrArg R hg'] at this
  have hkL : ¬ k₀ ≤ T.L := fun hle => by
    obtain ⟨g, hg, hne⟩ := UpperTheory.residual_characters_psi_ne Ω l c D T h.hyp.good h.hyp.ok h.hyp.two
    exact hne ((h.hyp.ps g).2 (IntermediateField.fixingSubgroup_le hle (hfix g hg.1)))
  have hKk : ¬ T.K ≤ k₀ := fun hle => by
    letI : Algebra T.K k₀ := (IntermediateField.inclusion hle).toRingHom.toAlgebra
    haveI : IsTotallyComplex k₀ := isTotallyComplex_of_algebra T.K k₀
    obtain ⟨w⟩ : Nonempty (InfinitePlace k₀) := inferInstance
    exact InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w) (IsTotallyReal.isReal w)
  haveI := T.nK.to_finiteDimensional
  haveI := T.nL.to_finiteDimensional
  haveI : FiniteDimensional ℚ k₀ := NumberField.to_finiteDimensional
  obtain ⟨E, hE⟩ : ∃ E : IntermediateField ℚ Ω, E = k₀ ⊔ T.K := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : IntermediateField ℚ Ω, M = k₀ ⊔ T.L := ⟨_, rfl⟩
  haveI : FiniteDimensional ℚ E := hE ▸ IntermediateField.finiteDimensional_sup k₀ T.K
  haveI : FiniteDimensional ℚ M := hM ▸ IntermediateField.finiteDimensional_sup k₀ T.L
  haveI : NumberField E := {}
  haveI : NumberField M := {}
  have hEM : E ≤ M := hE ▸ hM ▸ sup_le_sup_left hKL _
  have hKE : T.K ≤ E := hE ▸ le_sup_right
  have hkE : k₀ ≤ E := hE ▸ le_sup_left
  have hLM : T.L ≤ M := hM ▸ le_sup_right
  letI : Algebra T.K E := (IntermediateField.inclusion hKE).toRingHom.toAlgebra
  letI : Algebra k₀ E := (IntermediateField.inclusion hkE).toRingHom.toAlgebra
  letI : Algebra T.L M := (IntermediateField.inclusion hLM).toRingHom.toAlgebra
  letI : Algebra E M := (IntermediateField.inclusion hEM).toRingHom.toAlgebra
  haveI : IsScalarTower k₀ E Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower T.L M Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower E M Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℚ k₀ E := IsScalarTower.of_algebraMap_eq fun _ => by simp
  haveI : IsScalarTower ℚ T.L M := IsScalarTower.of_algebraMap_eq fun _ => by simp
  haveI : IsScalarTower ℚ E M := IsScalarTower.of_algebraMap_eq fun _ => by simp
  haveI : IsTotallyComplex E := isTotallyComplex_of_algebra T.K _
  haveI : IsTotallyComplex M := isTotallyComplex_of_algebra T.L _
  haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  haveI : IsAlgClosure M Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  haveI : Algebra.IsQuadraticExtension ℚ T.K := { finrank_eq_two' := T.degK }
  haveI hK : IsAbelianGalois ℚ T.K := IsAbelianGalois.of_isCyclic ℚ T.K
  haveI : Algebra.IsQuadraticExtension ℚ k₀ := { finrank_eq_two' := h.hyp.deg }
  haveI hk₀ : IsAbelianGalois ℚ k₀ := IsAbelianGalois.of_isCyclic ℚ k₀
  haveI hLa : IsAbelianGalois ℚ T.L := by
    have h := @GroundTheory.Global.isAbelianGalois_sup ℚ Ω _ _ _ _ T.F T.K
      T.nF.to_finiteDimensional T.nK.to_finiteDimensional T.abF hK
    rw [← T.hL] at h
    exact h
  haveI : IsAbelianGalois ℚ M := hM ▸ @GroundTheory.Global.isAbelianGalois_sup ℚ Ω _ _ _ _ k₀ T.L ‹_› ‹_› hk₀ hLa
  haveI : IsAbelianGalois E M := IsAbelianGalois.tower_top ℚ _ _
  haveI : Group.IsSolvable (M ≃ₐ[E] M) := Group.isSolvable_of_comm fun a b => mul_comm' a b
  have dE : Module.finrank k₀ E = 2 := deg_two T.K k₀ _ (hE.trans (sup_comm _ _)) T.degK hKk
  have dM : Module.finrank T.L M = 2 := deg_two k₀ T.L _ hM h.hyp.deg hkL
  obtain ⟨π, hatt, v, v', hv, hi, hi'⟩ := h.dat.att
  have hk := h.dat.hk
  have ht := h.dat.ht
  have hreg : π.IsRegAlg := fun w => by
    rcases two_places h.hyp.deg hv w with rfl | rfl
    · exact ⟨_, hi, inf_reg _ (by simp; omega)⟩
    · exact ⟨_, hi', inf_reg _ (by simp; omega)⟩
  have RE := resFacts k₀ E Ω l 2 r
  have RM := resFacts E M Ω l 2 (r.comp (galEmb k₀ E Ω))
  obtain ⟨P₁, reg₁, att₁, inf₁⟩ := hQ k₀ E Ω l ι dE r π h.dat.cont hreg hatt (RE.2.2.2.1.1 (h.dat.irr _ RE.2.1))
  obtain ⟨P, reg, att, inf⟩ := hS E M Ω l ι _ P₁ (h.dat.cont.comp RE.1) reg₁ att₁
    (RM.2.2.2.1.1 (RE.2.2.2.2.1 h.dat.irr _ RM.2.1))
  haveI : IsCMField M := IsCMField.of_isAbelianGalois M
  haveI : IsAbelianGalois T.L M := IsAbelianGalois.tower_top ℚ _ _
  have hMfix : ∀ s : G T.L Ω, resQ T.L s ∈ k₀.fixingSubgroup → ∀ x : M, s (algebraMap M Ω x) = algebraMap M Ω x := fun s hs x => by
    have : resQ T.L s ∈ M.fixingSubgroup := by
      rw [hM, IntermediateField.fixingSubgroup_sup]
      exact ⟨hs, (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => s.commutes ⟨y, hy⟩⟩
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 this x x.2
  have hsp : ∀ (p : ℕ) (v : HeightOneSpectrum (𝓞 T.L)), S2.SplitIn p k₀ → ((p : ℕ) : 𝓞 T.L) ∈ v.asIdeal → UpperTheory.ConvolutionTheory.GM.Split M v :=
    fun p v hp hv => splitOfDec T.L M Ω v fun A hA s hs => hMfix s (hp A ((val_of_mem hA p).2 hv) hs)
  have hpol : Sol.Pol ι ((r.comp (galEmb k₀ E Ω)).comp (galEmb E M Ω)) := by
    obtain ⟨m, hm⟩ := h.hyp.two.ord
    refine UpperTheory.solvable_polarized_restriction E M Ω l ι 2 _ (UpperTheory.solvable_polarized_restriction k₀ E Ω l ι 2 r (_root_.UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.polMix_alt H Ω l k₀ ι _ k t r h.dat ⟨2 ^ m, by positivity, ?_⟩))
    refine MonoidHom.ext fun g => ?_
    rw [MonoidHom.pow_apply, S2.up, MonoidHom.comp_apply, ← map_pow, ← MonoidHom.pow_apply, hm, MonoidHom.one_apply, map_one,
      MonoidHom.one_apply]
  haveI : IsAbelianGalois ℚ E := IsAbelianGalois.tower_bot ℚ E M
  haveI : IsCMField E := IsCMField.of_isAbelianGalois E
  have hW : AllW ι ((r.comp (galEmb k₀ E Ω)).comp (galEmb E M Ω)) := by
    haveI : IsAlgClosure k₀ Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
    have h1 : Sd.IsAlgChar ι (1 : G E Ω →* (Qbar l)ˣ) := by simpa using (_root_.UpperTheory.V.Sd.alg_cyclotomic_of_printed_results H.toClassicalTheorems E Ω l ι).1 0 1 (by rw [MonoidHom.ker_one]; exact isOpen_univ)
    have h2 := _root_.UpperTheory.V.Z.Win.Birth.awChain_of_printsH H k₀ E M Ω dE l ι r 1 h.dat.cont hrw h1 (RM.2.2.2.1.1 (RE.2.2.2.2.1 h.dat.irr _ RM.2.1))
    have e : tw (r.comp (galEmb k₀ E Ω)) 1 = r.comp (galEmb k₀ E Ω) := MonoidHom.ext fun g => Units.ext (by rw [tw_val]; simp)
    rwa [e] at h2
  have hbad : SplitBad T.L P := fun v hv => by
    refine ⟨unrOfIne T.L M Ω v fun A _ s hs => hMfix s ?_, fun w hw => ?_⟩
    · let g : G T.F Ω := AlgEquiv.ofRingEquiv (f := s.toRingEquiv) fun x => s.commutes ⟨x, T.F_le x.2⟩
      exact (h.hyp.ps g).1 (h.hyp.two.unr A g ⟨hs.1, hs.2⟩)
    · have hn : ∀ p : ℕ, S2.SplitIn p k₀ → ((p : ℕ) : 𝓞 M) ∉ w.asIdeal := fun p hp hm => hv (hsp p v hp (by
        rw [← hw]
        change algebraMap (𝓞 T.L) (𝓞 M) p ∈ w.asIdeal
        rwa [map_natCast]))
      obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
      haveI : IsAlgClosure k₀ Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
      refine _root_.UpperTheory.V.Z.Win.Birth.sphOfUnrW_alt H M Ω l ι 2 one_le_two _ P ((h.dat.cont.comp RE.1).comp RM.1) hpol reg att
        hW w (hn l h.hyp.spl) A hA fun s hs => ?_
      obtain ⟨g, hg⟩ := h.dat.away A (mt (val_of_mem hA l).1 (hn l h.hyp.spl))
      have h2 : D.ξ (resQ k₀ (galEmb k₀ E Ω (galEmb E M Ω s))) = 1 :=
        h.hyp.two.xi A (fun p hp => by
          rw [Finset.mem_singleton.1 hp]
          exact mt (val_of_mem hA 2).1 (hn 2 h.hyp.sp2)) ⟨hs.1, hs.2⟩
      have h3 := hg (galEmb k₀ E Ω (galEmb E M Ω s)) ⟨hs.1, hs.2⟩
      have h5 : (S2.up D.ξ).comp (resQ k₀) (galEmb k₀ E Ω (galEmb E M Ω s)) = 1 := by
        rw [MonoidHom.comp_apply, S2.up, MonoidHom.comp_apply, h2, map_one]
      generalize (S2.up D.ξ).comp (resQ k₀) = y at h3 h5
      have h4 : g * r (galEmb k₀ E Ω (galEmb E M Ω s)) * g⁻¹ = 1 := Units.ext (h3.trans (by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h5]))
      exact mul_left_cancel (a := g) (by rw [mul_one]; exact mul_inv_eq_one.1 h4)
  refine (fun h1 h2 => And.intro (hI T.L M Ω dM l ι P _ att h1 hbad _ ((UpperTheory.galoisRep_irreducibility_criterion.1 _ Unit _ 4 _).2.1 hL) h2)
    (awInd T.L M Ω dM l ι P _ att (hW P reg att) hbad _ h2)) (fun ψ => ?_) fun s hs => ?_
  · obtain ⟨τ, τ', hne, e, e'⟩ := two_emb dM ψ
    let pl : (M →+* ℂ) → InfinitePlace k₀ := fun τ =>
      InfinitePlace.mk ((τ.comp (algebraMap E M)).comp (algebraMap k₀ E))
    have hpl : ∀ τ m, π.HasInfChar (pl τ) m → P.HasInfChar τ m := fun τ m hm => inf τ m (inf₁ _ m hm)
    have hd : pl τ ≠ pl τ' := fun hp => by
      refine hne (hom_ext_sup k₀ T.L M (hkE.trans hEM) hLM hM.le τ τ' (fun x => ?_) fun x => DFunLike.congr_fun (e.trans e'.symm) x)
      rcases InfinitePlace.mk_eq_iff.1 hp with hp | hp
      · exact DFunLike.congr_fun hp x
      · rw [ComplexEmbedding.isReal_iff.1 (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _))] at hp
        exact DFunLike.congr_fun hp x
    have hinj : Function.Injective ![![(k : ℤ) + t, -(t : ℤ)] 0, ![(k : ℤ) + t, -(t : ℤ)] 1, ![(k : ℤ), 0] 0, ![(k : ℤ), 0] 1] := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> first | rfl | (simp at hij <;> omega)
    rcases two_places h.hyp.deg hv (pl τ) with p | p <;> rcases two_places h.hyp.deg hv (pl τ') with p' | p'
    · exact absurd (p.trans p'.symm) hd
    · exact ⟨_, _, τ, τ', hne, e, e', hpl _ _ (p ▸ hi), hpl _ _ (p' ▸ hi'), hinj⟩
    · exact ⟨_, _, τ', τ, hne.symm, e', e, hpl _ _ (p' ▸ hi), hpl _ _ (p ▸ hi'), hinj⟩
    · exact absurd (p.trans p'.symm) hd
  · have hs' : resQ T.L s ∉ (resQ k₀).range := by
      rintro ⟨u, hu⟩
      apply hs
      rw [range_galEmb]
      have : resQ T.L s ∈ M.fixingSubgroup := by
        rw [hM, IntermediateField.fixingSubgroup_sup]
        exact ⟨(IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => hu ▸ u.commutes ⟨y, hy⟩,
          (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => s.commutes ⟨y, hy⟩⟩
      exact fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 this x x.2
    obtain ⟨c1, c2⟩ := UpperTheory.symmetric_square_mixed_charpoly _ _ _ _ _ _ _ _ _ h.mix _ hs'
    refine ⟨fun g g' e => c1 (galEmb k₀ E Ω (galEmb E M Ω g)) (galEmb k₀ E Ω (galEmb E M Ω g')) ?_,
      fun g e => c2 (galEmb k₀ E Ω (galEmb E M Ω g)) ?_⟩
    · have := congrArg (resQ T.L) e
      rw [map_mul, map_mul, map_inv] at this
      exact this
    · have := congrArg (resQ T.L) e
      rw [map_mul] at this
      exact this
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published UpperTheory.V.Sd UpperTheory.V.Ws UpperTheory.V.Z.Bc UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.indAutLP_of_printsH_upQuad_upSol_indCs (H : _root_.UpperTheory.V.Af.HypothesesH') (hQ : UpQuadI) (hS : UpSolI) (hI : IndCs) : _root_.UpperTheory.V.Z.Win.Birth.IndAutLP :=
  _root_.UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.indAutLP_of_upQuad_upSol_indAutCs H hQ hS (_root_.UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.indAutCs_of_alt H.toClassicalTheorems hI)
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.V.Z.Bc
theorem seedIIs_alt (hH : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Ws.SeedIIAlt :=
  have hA := hH.toClassicalTheorems
  _root_.UpperTheory.V.Z.Bc.seedII_Z_alt ⟨hH, Published.hilbert_eisenstein_weight_one_holds, Lit.oneUse⟩
    (_root_.UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.indAutLP_of_printsH_upQuad_upSol_indCs hH (_root_.UpperTheory.V.Z.Bc.upQuadI_of_alt hA (quadLiftRealToComplex_of_base_change hH.bc)) (_root_.UpperTheory.V.Z.Bc.upSolI_of_alt hA (cyclicLiftRankTwo_of_cyclic_base_change hH.cyc)) indCs)
end UpperTheory.V.Z.Bc
end
end
