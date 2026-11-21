import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LocalValuationColumns
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValuationLowerBoundHostFieldAllPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGermOnColumnsSameValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGermOnCopiesSameValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFactorDepthInChartChartIndependent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFactorDepthInChartIndependentClosedField
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsExpEqOfSubstLg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupOperatorDepthMulDisjointColumns
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupExpTwoSidedInverseUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDeterminantPowDepthBounds
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NabValNEqSumCoeff
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCombinationIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.FiniteNotLocFrOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormEqNegOne
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TotalDegreeLeAndExistsCombinationOfMemFFV
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.DescentPf

section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CharDepth GlobalTheory.FactorDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detFactorDepthInChart_chart_independent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch Ch' : IntegralChartA3 Xo c T io y) (X : ValExt T p) (f : Lt1 Dw) (k : ℕ), nuFacC Ch X f k = nuFacC Ch' X f k := by
  first | exact @GlobalTheory.FactorDepth.nuFacC_chart_indep | exact GlobalTheory.FactorDepth.nuFacC_chart_indep | (intros; apply GlobalTheory.FactorDepth.nuFacC_chart_indep <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CharDepth GlobalTheory.FactorDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detFactorDepthInChart_independent_closedField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X X' : ValExt T p) (f : Lt1 Dw) (k : ℕ), nuFacC Ch X f k = nuFacC Ch X' f k := by
  first | exact @GlobalTheory.DepthField.nuFacC_field | exact GlobalTheory.DepthField.nuFacC_field | (intros; apply GlobalTheory.DepthField.nuFacC_field <;> assumption)
end

section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupOperatorDepth_mul_disjoint_columns : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (κ : Type) [Fintype κ] [DecidableEq κ] (d : κ → ℕ) (G : ∀ b, LogFGL v (d b)) (ι : κ → Type) [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)] (u : ∀ b, ι b → Fin (d b) → C) (S : Set κ) (P Q : MvPolynomial (Σ b, ι b) C), (∀ x ∈ P.vars, x.1 ∈ S) → (∀ x ∈ Q.vars, x.1 ∉ S) → depth G u (P * Q) = depth G u P + depth G u Q := by
  first | exact @GlobalTheory.FGDepth.depth_mul_of_disjoint_columns | exact GlobalTheory.FGDepth.depth_mul_of_disjoint_columns | (intros; apply GlobalTheory.FGDepth.depth_mul_of_disjoint_columns <;> assumption)
end

section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

noncomputable section

variable {C : Type} [Field C]

theorem coeff_subst_extend_zero {σ τ : Type} [Finite σ] {j : τ → σ} (hj : Function.Injective j)
    (g : MvPowerSeries σ C) (α : τ →₀ ℕ) :
    coeff α (subst (Function.extend j (X : τ → MvPowerSeries τ C) 0) g) =
      coeff (Finsupp.mapDomain j α) g := by
  classical
  have hc : ∀ s, constantCoeff (Function.extend j (X : τ → MvPowerSeries τ C) 0 s) = 0 := by
    intro s
    rw [Function.extend_def]
    split_ifs <;> simp
  have ha := hasSubst_of_constantCoeff_zero hc
  rw [coeff_subst ha, finsum_eq_single _ (Finsupp.mapDomain j α)]
  · rw [Finsupp.prod_mapDomain_index_inj hj]
    simp only [hj.extend_apply]
    rw [← MvPowerSeries.monomial_one_eq, coeff_monomial_same, smul_eq_mul, mul_one]
  · intro D hD
    by_cases hsupp : ↑D.support ⊆ Set.range j
    · obtain ⟨β, rfl⟩ : ∃ β, Finsupp.mapDomain j β = D :=
        ⟨_, Finsupp.mapDomain_comapDomain j hj D hsupp⟩
      rw [Finsupp.prod_mapDomain_index_inj hj]
      simp only [hj.extend_apply]
      rw [← MvPowerSeries.monomial_one_eq, coeff_monomial_ne, smul_zero]
      rintro rfl
      exact hD rfl
    · obtain ⟨s, hs, hsr⟩ := Set.not_subset.mp hsupp
      have hz : Function.extend j (X : τ → MvPowerSeries τ C) 0 s = 0 :=
        Function.extend_apply' _ _ _ (fun h => hsr h)
      have hs' : D s ≠ 0 := Finsupp.mem_support_iff.mp hs
      rw [Finsupp.prod, Finset.prod_eq_zero hs (by simp [hz, hs']), map_zero, smul_zero]

theorem subst_zero_of_constantCoeff {σ τ : Type} [Finite σ] (h : MvPowerSeries σ C)
    (h0 : constantCoeff h = 0) : subst (0 : σ → MvPowerSeries τ C) h = 0 := by
  exact subst_zero_of_constantCoeff_zero h0

theorem subst_sum_smul_X {σ τ ι : Type} [Fintype ι] {s : σ → MvPowerSeries τ C} (hs : HasSubst s)
    (c : ι → C) (k : ι → σ) :
    subst s (∑ a, c a • (X (k a) : MvPowerSeries σ C)) = ∑ a, c a • s (k a) := by
  rw [← coe_substAlgHom hs, map_sum]
  simp only [map_smul, substAlgHom_X]

end

end GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

noncomputable section

variable {C : Type} [Field C] [CharZero C] {v : AddValuation C (WithTop ℝ)}

theorem constantCoeff_expAlong {κ : Type} {d : κ → ℕ} (G : ∀ b, LogFGL v (d b)) {ι : κ → Type}
    [∀ b, Fintype (ι b)] (u : ∀ b, ι b → Fin (d b) → C) (x : Σ b, Fin (d b)) :
    constantCoeff (expAlong G u x) = 0 := by
  have hE := (GlobalTheory.T.formalGroupExp_twoSided_inverse_unique C v (d x.1) (G x.1)).1
  unfold IsExp at hE
  simp only [expAlong]
  refine constantCoeff_subst_eq_zero ?_ ?_ (hE.1 x.2)
  · exact hasSubst_of_constantCoeff_zero (fun e => by simp [MvPowerSeries.smul_eq_C_mul])
  · intro e
    simp [MvPowerSeries.smul_eq_C_mul]

theorem depth_rename (κ : Type) [Fintype κ] [DecidableEq κ] (d : κ → ℕ)
    (G : ∀ b, LogFGL v (d b)) (ι : κ → Type) [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)]
    (u : ∀ b, ι b → Fin (d b) → C) (κ' : Type) [Fintype κ'] [DecidableEq κ'] (e : κ' ↪ κ)
    (P : MvPolynomial (Σ b : κ', ι (e b)) C) :
    depth G u (MvPolynomial.rename (fun x => (⟨e x.1, x.2⟩ : Σ b, ι b)) P) =
      depth (fun b => G (e b)) (fun b => u (e b)) P := by
  have hinj : ∀ (β : κ → Type),
      Function.Injective (fun x : (Σ b : κ', β (e b)) => (⟨e x.1, x.2⟩ : Σ b, β b)) := by
    intro β
    rintro ⟨a, x⟩ ⟨c, y⟩ h
    simp only [Sigma.mk.inj_iff] at h
    obtain ⟨h1, h2⟩ := h
    obtain rfl := e.injective h1
    rw [heq_eq_eq] at h2
    rw [h2]
  have hjt : Function.Injective (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) := hinj ι
  have hjv : Function.Injective (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) := hinj (fun b => Fin (d b))
  have hcc : ∀ {σ τ : Type} (j : τ → σ) (s : σ),
      constantCoeff (Function.extend j (X : τ → MvPowerSeries τ C) 0 s) = 0 := by
    intro σ τ j s
    classical
    rw [Function.extend_def]
    split_ifs <;> simp
  have hE : ∀ b (k : Fin (d b)), constantCoeff (expOf (G b) k) = 0 := by
    intro b k
    have h := (GlobalTheory.T.formalGroupExp_twoSided_inverse_unique C v (d b) (G b)).1
    unfold IsExp at h
    exact h.1 k
  have hA : HasSubst (expAlong G u) := hasSubst_of_constantCoeff_zero (constantCoeff_expAlong G u)
  have hA' : HasSubst (expAlong (fun b => G (e b)) (fun b => u (e b))) :=
    hasSubst_of_constantCoeff_zero (constantCoeff_expAlong _ _)
  have hRt : HasSubst (Function.extend (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) (X : (Σ b : κ', ι (e b)) → MvPowerSeries (Σ b : κ', ι (e b)) C) 0) :=
    hasSubst_of_constantCoeff_zero (hcc _)
  have hRv : HasSubst (Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0) :=
    hasSubst_of_constantCoeff_zero (hcc _)
  have hin : ∀ b, HasSubst (fun e' : Fin (d b) =>
      ∑ a, u b a e' • (X ⟨b, a⟩ : MvPowerSeries (Σ b, ι b) C)) := fun b =>
    hasSubst_of_constantCoeff_zero (fun e' => by simp [MvPowerSeries.smul_eq_C_mul])

  have K1 : ∀ F : MvPowerSeries (Σ b, ι b) C,
      derivAt0 (MvPolynomial.rename (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) P) F =
        derivAt0 P (subst (Function.extend (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) (X : (Σ b : κ', ι (e b)) → MvPowerSeries (Σ b : κ', ι (e b)) C) 0) F) := by
    intro F
    unfold derivAt0
    rw [MvPolynomial.support_rename_of_injective hjt,
      Finset.sum_image (Finsupp.mapDomain_injective hjt).injOn]
    refine Finset.sum_congr rfl fun α _ => ?_
    have hm : (mfact (Finsupp.mapDomain (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) α) : C) = mfact α := by
      unfold mfact
      exact Finsupp.prod_mapDomain_index_inj hjt
    rw [MvPolynomial.coeff_rename_mapDomain _ hjt, coeff_subst_extend_zero hjt, hm]

  have K2 : ∀ x : Σ b, Fin (d b),
      subst (Function.extend (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) (X : (Σ b : κ', ι (e b)) → MvPowerSeries (Σ b : κ', ι (e b)) C) 0) (expAlong G u x) =
        subst (expAlong (fun b => G (e b)) (fun b => u (e b))) (Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0 x) := by
    rintro ⟨b, k⟩
    by_cases hb : ∃ b', e b' = b
    · obtain ⟨b', rfl⟩ := hb
      have h1 : Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0 ⟨e b', k⟩ = X ⟨b', k⟩ := hjv.extend_apply _ _ ⟨b', k⟩
      have h2 : ∀ a, Function.extend (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) (X : (Σ b : κ', ι (e b)) → MvPowerSeries (Σ b : κ', ι (e b)) C) 0 ⟨e b', a⟩ = X ⟨b', a⟩ :=
        fun a => hjt.extend_apply _ _ ⟨b', a⟩
      rw [h1, subst_X hA']
      simp only [expAlong]
      rw [subst_comp_subst_apply (hin (e b')) hRt]
      congr 1
      funext e'
      rw [subst_sum_smul_X hRt]
      simp only [h2]
    · have h1 : Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0 ⟨b, k⟩ = 0 :=
        Function.extend_apply' _ _ _ (by
          rintro ⟨⟨b', k'⟩, h⟩
          exact hb ⟨b', congrArg Sigma.fst h⟩)
      have h2 : ∀ a, Function.extend (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) (X : (Σ b : κ', ι (e b)) → MvPowerSeries (Σ b : κ', ι (e b)) C) 0 ⟨b, a⟩ = 0 := fun a =>
        Function.extend_apply' _ _ _ (by
          rintro ⟨⟨b', a'⟩, h⟩
          exact hb ⟨b', congrArg Sigma.fst h⟩)
      rw [h1, ← coe_substAlgHom hA', map_zero]
      simp only [expAlong]
      rw [subst_comp_subst_apply (hin b) hRt]
      have h3 : (fun e' : Fin (d b) => subst (Function.extend (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) (X : (Σ b : κ', ι (e b)) → MvPowerSeries (Σ b : κ', ι (e b)) C) 0)
          (∑ a, u b a e' • (X ⟨b, a⟩ : MvPowerSeries (Σ b, ι b) C))) = 0 := by
        funext e'
        rw [subst_sum_smul_X hRt]
        simp [h2]
      rw [h3]
      exact subst_zero_of_constantCoeff _ (hE b k)
  have K : ∀ f : MvPowerSeries (Σ b, Fin (d b)) C,
      derivAt0 (MvPolynomial.rename (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) P) (subst (expAlong G u) f) =
        derivAt0 P (subst (expAlong (fun b => G (e b)) (fun b => u (e b))) (subst (Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0) f)) := by
    intro f
    rw [K1, subst_comp_subst_apply hA hRt, subst_comp_subst_apply hRv hA']
    exact congrArg (fun F => derivAt0 P (subst F f)) (funext K2)

  have Rint : ∀ f : MvPowerSeries (Σ b, Fin (d b)) C, MvIsInt v f →
      MvIsInt v (subst (Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0) f) := by
    intro f hf α
    rw [coeff_subst_extend_zero hjv]
    exact hf _
  have Rsec : ∀ g : MvPowerSeries (Σ b : κ', Fin (d (e b))) C, MvIsInt v g →
      ∃ f, MvIsInt v f ∧ subst (Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0) f = g := by
    intro g hg
    classical
    refine ⟨@id (MvPowerSeries (Σ b, Fin (d b)) C)
      (Function.extend (Finsupp.mapDomain (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b)))) (fun α => coeff α g) 0), ?_, ?_⟩
    · intro β
      show IsIntV v (Function.extend (Finsupp.mapDomain (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b)))) (fun α => coeff α g) 0 β)
      rw [Function.extend_def]
      split_ifs with h
      · exact hg _
      · simp [IsIntV]
    · ext α
      rw [coeff_subst_extend_zero hjv]
      exact (Finsupp.mapDomain_injective hjv).extend_apply _ _ α
  unfold depth
  apply le_antisymm
  · refine le_iInf fun g => ?_
    obtain ⟨f, hf, hfg⟩ := Rsec g.1 g.2
    refine (iInf_le _ ⟨f, hf⟩).trans_eq ?_
    dsimp only
    rw [K f, hfg]
  · refine le_iInf fun f => ?_
    refine (iInf_le _ ⟨subst (Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0) f.1, Rint f.1 f.2⟩).trans_eq ?_
    dsimp only
    rw [K f.1]

end

end GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem depth_restrict : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (κ : Type) [Fintype κ] [DecidableEq κ] (d : κ → ℕ) (G : ∀ b, LogFGL v (d b)) (ι : κ → Type) [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)] (u : ∀ b, ι b → Fin (d b) → C) (κ' : Type) [Fintype κ'] [DecidableEq κ'] (e : κ' ↪ κ) (P : MvPolynomial (Σ b : κ', ι (e b)) C), depth G u (MvPolynomial.rename (fun x => (⟨e x.1, x.2⟩ : Σ b, ι b)) P) = depth (fun b => G (e b)) (fun b => u (e b)) P := by
  intro C _ _ v κ _ _ d G ι _ _ u κ' _ _ e P
  exact depth_rename κ d G ι u κ' e P

end GlobalTheory.FGDepth
end

section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentialOperatorDepth_restrict_columns : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (κ : Type) [Fintype κ] [DecidableEq κ] (d : κ → ℕ) (G : ∀ b, LogFGL v (d b)) (ι : κ → Type) [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)] (u : ∀ b, ι b → Fin (d b) → C) (κ' : Type) [Fintype κ'] [DecidableEq κ'] (e : κ' ↪ κ) (P : MvPolynomial (Σ b : κ', ι (e b)) C), depth G u (MvPolynomial.rename (fun x => (⟨e x.1, x.2⟩ : Σ b, ι b)) P) = depth (fun b => G (e b)) (fun b => u (e b)) P := by
  first | exact @GlobalTheory.FGDepth.depth_restrict | exact GlobalTheory.FGDepth.depth_restrict | (intros; apply GlobalTheory.FGDepth.depth_restrict <;> assumption)
end

section
set_option autoImplicit false

namespace GlobalTheory.FactorDepthProd

section General

open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {κ : Type} [Fintype κ] {d : κ → ℕ}
  (G : ∀ b, LogFGL v (d b)) {ι : κ → Type} [∀ b, Fintype (ι b)] (u : ∀ b, ι b → Fin (d b) → C)

omit [Fintype κ] in

theorem constantCoeff_expAlong (x : Σ b, Fin (d b)) : constantCoeff (expAlong G u x) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (by simp)) (by simp) ((isExp_expOf _).1 _)

theorem derivAt0_one_subst (f : MvPowerSeries (Σ b, Fin (d b)) C) :
    derivAt0 1 (subst (expAlong G u) f) = constantCoeff f := by
  classical
  have hs : HasSubst (expAlong G u) := hasSubst_of_constantCoeff_zero (constantCoeff_expAlong G u)
  have h0 : constantCoeff (subst (expAlong G u) (f - (constantCoeff f) • 1)) = 0 :=
    constantCoeff_subst_eq_zero hs (constantCoeff_expAlong G u) (by simp)
  rw [← coe_substAlgHom hs, map_sub, map_smul, map_one, coe_substAlgHom hs] at h0
  unfold derivAt0
  rw [MvPolynomial.support_one, Finset.sum_singleton]
  simpa [mfact, sub_eq_zero] using h0

theorem depth_one : depth G u 1 = 0 := by
  classical
  unfold depth
  refine le_antisymm (iInf_le_of_le ⟨1, fun α => ?_⟩ ?_) (le_iInf fun f => ?_)
  · unfold IsIntV; rw [coeff_one]; split_ifs <;> simp
  · rw [derivAt0_one_subst, map_one, AddValuation.map_one]; rfl
  · rw [derivAt0_one_subst]
    have h : (0 : WithTop ℝ) ≤ v (constantCoeff f.1) := f.2 0
    exact WithBot.coe_le_coe.2 h

theorem depth_prod [CharZero C] [DecidableEq κ] [∀ b, DecidableEq (ι b)] {F : Type} (col : κ → F)
    (P : F → MvPolynomial (Σ b, ι b) C) (hP : ∀ f, ∀ x ∈ (P f).vars, col x.1 = f) (s : Finset F) :
    depth G u (∏ f ∈ s, P f) = ∑ f ∈ s, depth G u (P f) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using depth_one G u
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ← ih]
    refine GlobalTheory.T.formalGroupOperatorDepth_mul_disjoint_columns C v κ d G ι u {b | col b = a} _ _ (hP a) fun x hx h => ?_
    obtain ⟨f, hf, hxf⟩ := Finset.mem_biUnion.1 (MvPolynomial.vars_prod _ hx)
    exact ha ((show col x.1 = a from h) ▸ hP f x hxf ▸ hf)

theorem depth_prod_detPow [CharZero C] {n : ℕ} (G₀ : LogFGL v n) {F : Type} [Fintype F] (r : F → ℕ)
    (w : ∀ f, Fin (r f) → Fin n → C) (cx : F → ℕ) :
    depth (fun _ : (Σ f : F, Fin (r f)) => G₀) (fun b => w b.1)
      (∏ f : F, MvPolynomial.rename (fun ℓ : (Σ _ : Fin (r f), Fin (r f)) =>
        (⟨⟨f, ℓ.1⟩, ℓ.2⟩ : Σ b : (Σ f : F, Fin (r f)), Fin (r b.1))) (detPow C (r f) (cx f))) =
      ∑ f : F, detDepth G₀ (w f) (cx f) := by
  classical
  rw [depth_prod _ _ (fun b : (Σ f : F, Fin (r f)) => b.1)]
  · refine Finset.sum_congr rfl fun f _ => ?_
    have h := GlobalTheory.T.differentialOperatorDepth_restrict_columns C v (Σ f : F, Fin (r f)) (fun _ => n) (fun _ => G₀)
      (fun b => Fin (r b.1)) (fun b => w b.1) (Fin (r f)) ⟨fun b => ⟨f, b⟩, fun _ _ h => eq_of_heq (Sigma.mk.inj h).2⟩
      (detPow C (r f) (cx f))
    unfold detDepth
    refine Eq.trans ?_ (h.trans ?_)
    · congr 1
    · congr 1
  · intro f x hx
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 (MvPolynomial.vars_rename _ _ hx)
    rfl

end General

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CharDepth GlobalTheory.FactorDepth

theorem nuProdC_eq_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ), nuProdC Ch X cx = ∑ f : Lt1 Dw, nuFacC Ch X f (cx f) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p _ T io y Ch X cx
  exact depth_prod_detPow (fgl Ch X) rk (frame Ch X) cx

end GlobalTheory.FactorDepthProd
end

section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CharDepth GlobalTheory.FactorDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detProductDepthInChart_eq_sum_factorDepths : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ), nuProdC Ch X cx = ∑ f : Lt1 Dw, nuFacC Ch X f (cx f) := by
  first | exact @GlobalTheory.FactorDepthProd.nuProdC_eq_sum | exact GlobalTheory.FactorDepthProd.nuProdC_eq_sum | (intros; apply GlobalTheory.FactorDepthProd.nuProdC_eq_sum <;> assumption)
end

section
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CharDepth GlobalTheory.FactorDepth

namespace GlobalTheory.FactorDepth

theorem nuFac_eq_nuFacC_and_nuProd_eq_nuP :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing;
      ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io)
        (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p),
        (∀ (f : Lt1 Dw) (k : ℕ), nuFac p y f k = nuFacC Ch X f k) ∧
          ∀ cx : Lt1 Dw → ℕ, nuProd p y cx = nuP p y cx := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p _ T io y Ch X
  have hc : ∀ (Ch' : IntegralChartA3 Xo c T io y) (X' : ValExt T p) (f : Lt1 Dw) (k : ℕ),
      nuFacC Ch' X' f k = nuFacC Ch X f k := fun Ch' X' f k =>
    (GlobalTheory.T.detFactorDepthInChart_chart_independent E H Dw l Xo c p T io y Ch' Ch X' f k).trans
      (GlobalTheory.T.detFactorDepthInChart_independent_closedField E H Dw l Xo c p T io y Ch X' X f k)
  have h1 : ∀ (f : Lt1 Dw) (k : ℕ), nuFac p y f k = nuFacC Ch X f k := fun f k =>
    le_antisymm (nuFac_le Ch X f k) (le_nuFac fun Ch' X' => (hc Ch' X' f k).ge)
  refine ⟨h1, fun cx => ?_⟩
  have h2 : ∀ (Ch' : IntegralChartA3 Xo c T io y) (X' : ValExt T p), nuProdC Ch' X' cx = nuP p y cx := by
    intro Ch' X'
    rw [GlobalTheory.T.detProductDepthInChart_eq_sum_factorDepths E H Dw l Xo c p T io y Ch' X' cx, nuP]
    exact Finset.sum_congr rfl fun f _ => (hc Ch' X' f (cx f)).trans (h1 f (cx f)).symm
  exact le_antisymm (iInf_le_of_le Ch (iInf_le_of_le X (h2 Ch X).le))
    (le_iInf₂ fun Ch' X' => (h2 Ch' X').ge)

end GlobalTheory.FactorDepth
end

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CharDepth GlobalTheory.FactorDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detFactorDepth_eq_chart_value_and_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p), (∀ (f : Lt1 Dw) (k : ℕ), nuFac p y f k = nuFacC Ch X f k) ∧ ∀ cx : Lt1 Dw → ℕ, nuProd p y cx = nuP p y cx := by
  atlas_forward_decl GlobalTheory.FactorDepth.nuFac_eq_nuFacC_and_nuProd_eq_nuP
end

section
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.IsoFactorDepth

open GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns in

def colEmb {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    (cx : Lt1 Dw → ℕ) : Col cx ↪ (Σ f : Lt1 Dw, Fin (rk f)) where
  toFun b := ⟨b.1.1, b.2⟩
  inj' := by
    rintro ⟨⟨f, hf⟩, a⟩ ⟨⟨g, hg⟩, b⟩ h
    simp only [Sigma.mk.inj_iff] at h
    obtain ⟨rfl, h⟩ := h
    cases h
    rfl

open GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns in

theorem prodP_eq_rename_polyH {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (C : Type) [Field C] (cx : Lt1 Dw → ℕ) :
    prodP C cx = MvPolynomial.rename (fun x : Let cx =>
      (⟨colEmb cx x.1, x.2⟩ : Σ b : (Σ f : Lt1 Dw, Fin (rk f)), Fin (rk b.1))) (polyH C cx) := by
  classical
  unfold prodP polyH
  rw [map_prod]
  simp_rw [MvPolynomial.rename_rename]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun f : Lt1 Dw => cx f ≠ 0)]
  have h1 : ∏ f : {f : Lt1 Dw // ¬ cx f ≠ 0}, MvPolynomial.rename (fun ℓ : (Σ _ : Fin (rk f.1), Fin (rk f.1)) =>
      (⟨⟨f.1, ℓ.1⟩, ℓ.2⟩ : Σ b : (Σ f : Lt1 Dw, Fin (rk f)), Fin (rk b.1))) (GlobalTheory.FGDepth.detPow C (rk f.1) (cx f.1)) = 1 := by
    refine Finset.prod_eq_one fun f _ => ?_
    have h0 : cx f.1 = 0 := not_not.1 f.2
    rw [GlobalTheory.FGDepth.detPow, h0, pow_zero, map_one]
  rw [h1, mul_one]
  rfl

theorem nuH_vp_eq_nuP : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ), GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nuH_vp Ch X cx = nuP p y cx ∧ 0 ≤ nuP p y cx ∧ nuP p y cx ≠ ⊤ := by
  intro E _ _ _ H Dw l Xo c
  classical
  letI := H.starRing
  intro p _ T io y Ch X cx
  have hfac := (GlobalTheory.T.detFactorDepth_eq_chart_value_and_sum E H Dw l Xo c p T io y Ch X).1
  have hsum : nuP p y cx = ∑ f, nuFacC Ch X f (cx f) :=
    Finset.sum_congr rfl fun f _ => hfac f (cx f)
  have hbd : ∀ f, 0 ≤ nuFacC Ch X f (cx f) ∧
      nuFacC Ch X f (cx f) ≤ ((((rk f * cx f : ℕ) : ℝ) / (p - 1) : ℝ) : EReal) := fun f => by
    have h := GlobalTheory.T.formalGroupDeterminantPowDepth_bounds X.C (vX_vp X) p Fact.out (vX_vp_p X) (rk f) (chD Ch.ch) (cx f) (fgl Ch X)
      (frame Ch X f) (isSatFrame_frame Ch X f)
    refine ⟨h.1, h.2.2.trans (le_of_eq ?_)⟩
    push_cast; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hsum, ← GlobalTheory.FactorDepthProd.nuProdC_eq_sum]
    unfold nuProdC GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nuH_vp
    rw [prodP_eq_rename_polyH]
    exact (GlobalTheory.FGDepth.depth_restrict X.C (vX_vp X) (Σ f : Lt1 Dw, Fin (rk f)) (fun _ => chD Ch.ch)
      (fun _ => fgl Ch X) (fun b => Fin (rk b.1)) (fun b => frame Ch X b.1) (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.Col cx)
      (colEmb cx) (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.polyH X.C cx)).symm
  · rw [hsum]
    exact Finset.sum_nonneg fun f _ => (hbd f).1
  · rw [hsum]
    have hreal : ∃ r : ℝ, ∑ f, nuFacC Ch X f (cx f) = (r : EReal) := by
      refine Finset.sum_induction _ (fun x : EReal => ∃ r : ℝ, x = r) ?_ ⟨0, rfl⟩ ?_
      · rintro a b ⟨r, rfl⟩ ⟨s, rfl⟩
        exact ⟨r + s, (EReal.coe_add r s).symm⟩
      · intro f _
        have h0 := (hbd f).1
        have h1 := (hbd f).2
        refine ⟨(nuFacC Ch X f (cx f)).toReal, (EReal.coe_toReal ?_ ?_).symm⟩
        · exact ne_top_of_le_ne_top (EReal.coe_ne_top _) h1
        · exact ne_bot_of_le_ne_bot (by simp) h0
    obtain ⟨r, hr⟩ := hreal
    rw [hr]
    exact EReal.coe_ne_top r

end GlobalTheory.IsoFactorDepth
end

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicFactor_depth_eq_sum_factor_depths : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ), GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nuH_vp Ch X cx = nuP p y cx ∧ 0 ≤ nuP p y cx ∧ nuP p y cx ≠ ⊤ := by
  atlas_forward_decl GlobalTheory.IsoFactorDepth.nuH_vp_eq_nuP
end

section
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.DepthDescent

open GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns

theorem nuLocOf_eq_nuLocX_vp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ) (n : ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V), ∀ k : ℕ, nuLocOf Ch (vV T.V (p : T.Fr)).toNat k (polyT B cx) = GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nuLocX_vp Ch X cx B k := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p _ la T io e ho y Ch X cx n B k
  have hp0 : 0 ≤ vV T.V (p : T.Fr) := by
    have := GlobalTheory.vV_algebraMap_nonneg_dvr T (p : T.V)
    rwa [map_natCast] at this
  have he : vV T.V (p : T.Fr) = (((vV T.V (p : T.Fr)).toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg hp0).symm
  letI := io.toAlgebra
  letI : Algebra T.Fr X.C := X.ιF.toAlgebra
  have hh : MvPowerSeries.constantCoeff Ch.ch.h = 0 :=
    ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_eq_zero_of_vanish_first_axis _ Ch.ch.gauge.ax0 0 fun _ => rfl
  have hu : (fun (ℓ : LtN Dw n) => lieVec Ch X ⟨ℓ.1, ℓ.2.1⟩) =
      fun ℓ j => X.ιF (Ch.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ j) := by
    funext ℓ j
    simp only [lieVec, jX, RingHom.comp_apply]
    rw [Ch.gen.1.2.2.2.2.2.2]
  have himg : ∀ f : PS T.Fr n (chD Ch.ch), nabX Ch X cx B k (MvPowerSeries.map X.ιF f) =
      X.ιF (nabValN Ch.ch.B T.Fr Ch.ch.h H.w0 k f (fun ℓ : LtN Dw n => ℓ.2.2)
        (fun ℓ => Ch.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) (polyT B cx)) := by
    intro f
    unfold nabX
    rw [hu]
    exact GlobalTheory.ThetaLeast.nabValN_algebraMap T.Fr X.C _ _ Ch.ch.B Ch.ch.h hh H.w0 k n f _ _ _ _
  have hB : ∀ g : PS X.C n (chD Ch.ch), nabX Ch X cx B k g =
      nabValN (GlobalTheory.FBMap.mapFB X.ιF Ch.ch.B) X.C (MvPowerSeries.map X.ιF Ch.ch.h) H.w0 k g
        (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ => lieVec Ch X ⟨ℓ.1, ℓ.2.1⟩)
        (MvPolynomial.map X.ιF (polyT B cx)) := by
    intro g
    have h1 : (GlobalTheory.FBMap.mapFB X.ιF Ch.ch.B).FK X.C = Ch.ch.B.FK X.C := by
      funext i
      ext μ
      simp [FB.FK, FGLaw.mapF, GlobalTheory.FBMap.mapFB, GlobalTheory.FBMap.mapLaw, GlobalTheory.FBMap.mapPt, RingHom.algebraMap_toAlgebra]
    have h2 : ∀ b, (GlobalTheory.FBMap.mapFB X.ιF Ch.ch.B).actK X.C b = Ch.ch.B.actK X.C b := by
      intro b
      funext i
      ext μ
      simp [FB.actK, GlobalTheory.FBMap.mapFB, GlobalTheory.FBMap.mapAct, GlobalTheory.FBMap.mapPt, RingHom.algebraMap_toAlgebra]
    unfold nabX nabValN FB.hL
    rw [h1, h2]
  apply le_antisymm
  · unfold nuLocX_vp
    refine le_iInf fun g => ?_
    obtain ⟨S, hS⟩ := GlobalTheory.nabValN_eq_sum_coeff X.C _ _ (GlobalTheory.FBMap.mapFB X.ιF Ch.ch.B)
      (MvPowerSeries.map X.ιF Ch.ch.h) H.w0 k n (LtN Dw n) (fun ℓ : LtN Dw n => ℓ.2.2)
      (fun ℓ => lieVec Ch X ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map X.ιF (polyT B cx))
    have hμ : ∀ μ, nuLocOf Ch (vV T.V (p : T.Fr)).toNat k (polyT B cx) ≤
        toE (vX_vp X (nabX Ch X cx B k (MvPowerSeries.monomial μ (1 : X.C)))) := by
      intro μ
      have hmon : (MvPowerSeries.monomial μ (1 : X.C) : PS X.C n (chD Ch.ch))
          = MvPowerSeries.map X.ιF (MvPowerSeries.monomial μ (1 : T.Fr) : PS T.Fr n (chD Ch.ch)) := by
        rw [MvPowerSeries.map_monomial, map_one X.ιF]
      rw [hmon, himg, toE_vX_vp_ιF X he]
      unfold nuLocOf
      refine iInf₂_le_of_le (MvPowerSeries.monomial μ (1 : T.Fr)) (fun ρ => ?_) le_rfl
      classical
      rw [MvPowerSeries.coeff_monomial]
      split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _
    rw [hB, hS g.1]
    simp only [← hB]
    generalize nuLocOf Ch (vV T.V (p : T.Fr)).toNat k (polyT B cx) = ν at hμ ⊢
    induction ν using WithBot.recBotCoe with
    | bot => exact bot_le
    | coe w =>
      refine WithBot.coe_le_coe.2 ?_
      refine (vX_vp X).map_le_sum fun μ _ => ?_
      rw [(vX_vp X).map_mul]
      exact le_trans (WithBot.coe_le_coe.1 (hμ μ)) (le_add_of_nonneg_left (g.2 μ))
  · unfold nuLocOf nuLocX_vp
    refine le_iInf₂ fun f hf => ?_
    refine iInf_le_of_le ⟨MvPowerSeries.map X.ιF f, fun α => ?_⟩ (le_of_eq ?_)
    · obtain ⟨t, ht⟩ := hf α
      rw [MvPowerSeries.coeff_map, ← ht]
      exact isIntV_jX X t
    · rw [himg, toE_vX_vp_ιF X he]

end GlobalTheory.DepthDescent
end

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localDepth_over_dvr_eq_over_closed_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ) (n : ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V), ∀ k : ℕ, nuLocOf Ch (vV T.V (p : T.Fr)).toNat k (polyT B cx) = GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nuLocX_vp Ch X cx B k := by
  atlas_forward_decl GlobalTheory.DepthDescent.nuLocOf_eq_nuLocX_vp
end

section
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ColDepth

open GlobalTheory.FGDepth

section Ultra

variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))

theorem val_eq_of_lt_sub (x y : C) (h : v x < v (x - y)) : v y = v x := by
  have h1 : min (v x) (v (x - y)) ≤ v (x - (x - y)) := AddValuation.map_sub v _ _
  rw [sub_sub_cancel, min_eq_left h.le] at h1
  have h2 : min (v y) (v (x - y)) ≤ v (y + (x - y)) := AddValuation.map_add v _ _
  rw [add_sub_cancel] at h2
  rcases le_total (v y) (v (x - y)) with h3 | h3
  · rw [min_eq_left h3] at h2
    exact le_antisymm h2 h1
  · rw [min_eq_right h3] at h2
    exact absurd (lt_of_le_of_lt h2 h) (lt_irrefl _)

theorem iInf_le_of_approx {S U : Type} (a : S → C) (b : U → C)
    (h : ∀ (s : S) (N : ℕ), ∃ t, ((N : ℝ) : WithTop ℝ) ≤ v (a s - b t)) :
    ⨅ t, toE (v (b t)) ≤ ⨅ s, toE (v (a s)) := by
  refine le_iInf fun s => ?_
  by_cases hs : v (a s) = ⊤
  · rw [hs]
    exact le_top
  · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hs
    obtain ⟨N, hN⟩ := exists_nat_gt r
    obtain ⟨t, ht⟩ := h s N
    have hlt : v (a s) < v (a s - b t) :=
      lt_of_lt_of_le (by rw [← hr]; exact WithTop.coe_lt_coe.2 hN) ht
    rw [← val_eq_of_lt_sub v _ _ hlt]
    exact iInf_le _ t

theorem iInf_eq_of_approx {S U : Type} (a : S → C) (b : U → C)
    (h1 : ∀ (s : S) (N : ℕ), ∃ t, ((N : ℝ) : WithTop ℝ) ≤ v (a s - b t))
    (h2 : ∀ (t : U) (N : ℕ), ∃ s, ((N : ℝ) : WithTop ℝ) ≤ v (a s - b t)) :
    ⨅ s, toE (v (a s)) = ⨅ t, toE (v (b t)) := by
  refine le_antisymm ?_ (iInf_le_of_approx v a b h1)
  refine iInf_le_of_approx v b a fun t N => ?_
  obtain ⟨s, hs⟩ := h2 t N
  exact ⟨s, by rwa [AddValuation.map_sub_swap]⟩

end Ultra

theorem nuLocOf_eq_nuP : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (cx : Lt1 Dw → ℕ) (n : ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V), IsCols c T io p cx B → ∀ k : ℕ, nuLocOf Ch (vV T.V (p : T.Fr)).toNat k (polyT B cx) = nuP p y cx := by
  intro E _ _ _ H Dw l Xo c p _ la T io e ho y Ch cx n B hB k
  letI := H.starRing
  obtain ⟨X⟩ := nonempty_valExt_of_overLa la ho
  have hmid : GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nuLocX_vp Ch X cx B k = GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nuH_vp Ch X cx := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nuLocX_vp GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nuH_vp depth
    refine iInf_eq_of_approx (vX_vp X)
      (fun g : {g : PS X.C n (chD Ch.ch) // MvIsInt (vX_vp X) g} => GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nabX Ch X cx B k g.1)
      (fun f : {f : MvPowerSeries (Σ _ : GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.Col cx, Fin (chD Ch.ch)) X.C // MvIsInt (vX_vp X) f} =>
        derivAt0 (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.polyH X.C cx) (MvPowerSeries.subst (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.expH Ch X cx) f.1))
      (fun g N => ?_) (fun f N => ?_)
    · obtain ⟨f, hf, hN⟩ := GlobalTheory.T.exists_integral_germ_on_columns_same_value E H Dw l Xo c p la T io e ho y Ch X cx n B hB N k g.1 g.2
      exact ⟨⟨f, hf⟩, hN⟩
    · obtain ⟨g, hg, hN⟩ := GlobalTheory.T.exists_integral_germ_on_copies_same_value E H Dw l Xo c p la T io e ho y Ch X cx n B hB N k f.1 f.2
      exact ⟨⟨g, hg⟩, hN⟩
  exact (GlobalTheory.T.localDepth_over_dvr_eq_over_closed_field E H Dw l Xo c p la T io e ho y Ch X cx n B k).trans
    (hmid.trans (GlobalTheory.T.isotropicFactor_depth_eq_sum_factor_depths E H Dw l Xo c p T io y Ch X cx).1)

end GlobalTheory.ColDepth
end

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnPolynomial_localDepth_eq_placeDepth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (cx : Lt1 Dw → ℕ) (n : ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V), IsCols c T io p cx B → ∀ k : ℕ, nuLocOf Ch (vV T.V (p : T.Fr)).toNat k (polyT B cx) = nuP p y cx := by
  atlas_forward_decl GlobalTheory.ColDepth.nuLocOf_eq_nuP
end

section
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RefGlob

theorem sum_smul_mem_HaO {Ty : Type} {r : Ty → ℕ} {n : ℕ} {k : Type} [Field k] (O : Subring k) (cc : Ty → Ty)
    (isX : Ty → Prop) (a : Ty → ℕ → ℕ) {m : ℕ} (x : Fin m → k) (P : Fin m → MvPolynomial (Letter Ty r n) k)
    (hx : ∀ i, x i ∈ O) (hP : ∀ i, P i ∈ HaO r n k O cc isX a) : ∑ i, x i • P i ∈ HaO r n k O cc isX a := by
  classical
  refine ⟨⟨Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hP i).1.1, fun σ i i' hi t => ?_,
    fun q hq => ?_⟩, fun q => ?_⟩
  · rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, (hP j).1.2.1 σ i i' hi t]
  · obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 (MvPolynomial.support_sum hq)
    exact (hP j).1.2.2 q (MvPolynomial.support_smul hj)
  · rw [MvPolynomial.coeff_sum]
    exact O.sum_mem fun j _ => by
      rw [MvPolynomial.coeff_smul, smul_eq_mul]
      exact O.mul_mem (hx j) ((hP j).2 q)

theorem exists_integer_congr {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (T₀ : CDVR)
    (io₀ : K →+* T₀.Fr) (ho : OverLa w T₀.V io₀ 1)
    (hini : ∀ (T : CDVR) (io : K →+* T.Fr) (e : ℕ), OverLa w T.V io e → ∃ (g : T₀.V →+* T.V) (χ : T₀.Fr →+* T.Fr),
      IsLocalHom g ∧ χ.comp io₀ = io ∧ χ.comp (algebraMap T₀.V T₀.Fr) = (algebraMap T.V T.Fr).comp g ∧
        ∀ ϖ : T₀.V, Irreducible ϖ → vV (K' := T.Fr) T.V (algebraMap T.V T.Fr (g ϖ)) = e)
    (d : ℕ) (hd : d ≠ 0) (v : T₀.V) :
    ∃ (x : 𝓞 K) (z : T₀.V), io₀ (x : K) = algebraMap T₀.V T₀.Fr v + (d : T₀.Fr) * algebraMap T₀.V T₀.Fr z := by
  obtain ⟨k, h, e⟩ := GlobalTheory.DefPt.Model.denseIn_of_initial w T₀ io₀ hini (algebraMap T₀.V T₀.Fr v) (d : T₀.V) (Nat.cast_ne_zero.2 hd)
  have hval : ∀ y : K, valV T₀.V (io₀ y) = w.valuation K y := fun y => by
    rw [GlobalTheory.PlaceCompletion.valV_eq_pow_of_overLa ho, pow_one]
  have hk : io₀ k = algebraMap T₀.V T₀.Fr (v - d * h) := by rw [map_sub, e]; ring
  have hk1 : w.valuation K k ≤ 1 := by
    rw [← hval, hk]
    exact GlobalTheory.PlaceCompletion.valV_algebraMap_le_one _
  have hdK : (d : K) ≠ 0 := Nat.cast_ne_zero.2 hd
  have hd0 : w.valuation K (d : K) ≠ 0 := by simpa using hd
  obtain ⟨x, hx⟩ := w.exists_valuation_sub_lt_of_integer hk1 (Units.mk0 _ hd0)
  obtain ⟨z, hz⟩ := GlobalTheory.PlaceCompletion.exists_algebraMap_eq_of_valV_le_one (V := T₀.V)
    (x := io₀ ((algebraMap (𝓞 K) K x - k) / d)) (by
      rw [hval, map_div₀]
      exact div_le_one_of_le₀ hx.le zero_le)
  refine ⟨x, z - h, ?_⟩
  have h2 : io₀ (x : K) = io₀ k + (d : T₀.Fr) * algebraMap T₀.V T₀.Fr z := by
    rw [hz, ← map_natCast io₀, ← map_mul, ← map_add, mul_div_cancel₀ _ hdK]
    exact congrArg io₀ (by simp)
  rw [h2, hk]
  simp only [map_sub, map_mul, map_natCast]
  ring

section Push

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {c : Coeff l} {T₀ T : CDVR} (g : T₀.V →+* T.V) (χ : T₀.Fr →+* T.Fr)
  (hχ : ∀ x, χ (algebraMap T₀.V T₀.Fr x) = algebraMap T.V T.Fr (g x))

include hχ

theorem isCols_map {io₀ : c.F →+* T₀.Fr} {p n : ℕ} {cx : Lt1 Dw → ℕ} {B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T₀.V}
    (hB : IsCols c T₀ io₀ p cx B) : IsCols c T (χ.comp io₀) p cx fun f b j => g (B f b j) := by
  obtain ⟨blk, hb⟩ := hB
  refine ⟨blk, fun f => ?_⟩
  obtain ⟨h1, ⟨r, h2⟩, h3⟩ := hb f
  refine ⟨fun b j hj => (congrArg g (h1 b j hj)).trans (map_zero g), ⟨r, ?_⟩, fun N => ?_⟩
  · have := h2.map g
    rw [RingHom.map_det] at this
    exact this
  · obtain ⟨x, hx1, hx2, hx3⟩ := h3 N
    refine ⟨x, hx1, fun b j => ?_, hx3⟩
    obtain ⟨z, hz⟩ := hx2 b j
    refine ⟨g z, ?_⟩
    rw [RingHom.comp_apply, hz, hχ]
    simp only [map_add, map_mul, map_pow, map_natCast]

theorem map_polyT {n : ℕ} (cx : Lt1 Dw → ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T₀.V) :
    MvPolynomial.map χ (polyT B cx) = polyT (fun f b j => g (B f b j)) cx := by
  simp only [polyT, polyP, map_prod, map_pow]
  refine Finset.prod_congr rfl fun f _ => ?_
  rw [RingHom.map_det]
  congr 2
  ext ρ i : 2
  simp [GlobalTheory.CombMinor.cMat, hχ]

end Push

theorem exists_harmA_congr_polyT : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (a : (E →+* ℂ) × ℕ → ℕ), (∀ τ, Antitone fun i => a (τ, i)) → ∀ n : ℕ, ∑ f : Lt1 Dw, 2 * rk f ≤ n → ∀ N : ℕ, ∃ P₁ ∈ harmA (Dw := Dw) c a n, ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∃ (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V) (R : MvPolynomial (LtN Dw n) T.Fr), IsCols c T io p (gap Dw a) B ∧ R ∈ FFV (Dw := Dw) T a n ∧ MvPolynomial.map io P₁ = polyT B (gap Dw a) + ((p : T.Fr) ^ N) • R := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p hp la a ha n hn N
  obtain ⟨T₀, io₀, ho₀, -, hini⟩ := GlobalTheory.PlaceCompletion.exists_initial_completion c.F la.1
  obtain ⟨B₀, hB₀⟩ := GlobalTheory.IsoCols.exists_isCols E H Dw l Xo c p la T₀ io₀ 1 ho₀ (gap Dw a) n
    (le_trans (Finset.sum_le_sum fun f _ => by split_ifs <;> simp) hn)
  obtain ⟨-, k, cf, Pi, hPi, hsum⟩ := GlobalTheory.totalDegree_le_and_exists_combination_of_mem_FFV E H Dw l Xo c T₀ io₀ a n _
    (polyT_mem_FFV ha hB₀)
  choose x z hxz using fun i => exists_integer_congr la.1 T₀ io₀ ho₀ hini (p ^ N)
    (pow_ne_zero N hp.out.ne_zero) (cf i)
  refine ⟨∑ i, (x i : c.F) • Pi i, sum_smul_mem_HaO _ _ _ _ _ _ (fun i => (x i).2) hPi, fun T io e ho => ?_⟩
  obtain ⟨g, χ, -, rfl, h2, -⟩ := hini T io e ho
  have hχ : ∀ y, χ (algebraMap T₀.V T₀.Fr y) = algebraMap T.V T.Fr (g y) := RingHom.congr_fun h2
  refine ⟨fun f b j => g (B₀ f b j), ∑ i, algebraMap T.V T.Fr (g (z i)) • MvPolynomial.map (χ.comp io₀) (Pi i),
    isCols_map g χ hχ hB₀, sum_smul_mem_HaO _ _ _ _ _ _ (fun i => ⟨_, rfl⟩)
      (fun i => PullbackSections.ffvMap E H Dw l c a n _ (hPi i) T _), ?_⟩
  rw [← map_polyT g χ hχ, hsum, map_sum, map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_map, RingHom.comp_apply, hxz i,
    map_add, hχ, map_natCast, Nat.cast_pow, map_pow]
  ring

end GlobalTheory.RefGlob
end

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_harmonic_congr_column_polynomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (a : (E →+* ℂ) × ℕ → ℕ), (∀ τ, Antitone fun i => a (τ, i)) → ∀ n : ℕ, ∑ f : Lt1 Dw, 2 * rk f ≤ n → ∀ N : ℕ, ∃ P₁ ∈ harmA (Dw := Dw) c a n, ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∃ (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V) (R : MvPolynomial (LtN Dw n) T.Fr), IsCols c T io p (gap Dw a) B ∧ R ∈ FFV (Dw := Dw) T a n ∧ MvPolynomial.map io P₁ = polyT B (gap Dw a) + ((p : T.Fr) ^ N) • R := by
  atlas_forward_decl GlobalTheory.RefGlob.exists_harmA_congr_polyT
end

section
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PertDepth

theorem nval_neg_eq (T : CDVR) (e : ℕ) (x : T.Fr) : nval T.V e (-x) = nval T.V e x := by
  by_cases hx : x = 0
  · subst hx; rw [neg_zero]
  · rw [nval_of_ne (neg_ne_zero.2 hx), nval_of_ne hx]
    simp only [vV, Valuation.map_neg]

theorem iInf_nval_add_eq (T : CDVR) (e : ℕ) {ι : Type*} (Q : ι → Prop) (A D : ι → T.Fr) (M : EReal)
    (hD : ∀ i, Q i → M ≤ nval T.V e (D i)) (hA : ⨅ (i) (_ : Q i), nval T.V e (A i) < M) :
    ⨅ (i) (_ : Q i), nval T.V e (A i + D i) = ⨅ (i) (_ : Q i), nval T.V e (A i) := by
  set Y := ⨅ (i) (_ : Q i), nval T.V e (A i) with hY
  set X := ⨅ (i) (_ : Q i), nval T.V e (A i + D i) with hX
  have hge : min Y M ≤ X := le_iInf₂ fun i hi =>
    le_trans (min_le_min (iInf₂_le i hi) (hD i hi)) (nval_add e (A i) (D i))
  have hle : min X M ≤ Y := le_iInf₂ fun i hi => by
    have h1 := nval_add (V := T.V) e (A i + D i) (-D i)
    rw [add_neg_cancel_right, nval_neg_eq] at h1
    exact le_trans (min_le_min (iInf₂_le i hi) (hD i hi)) h1
  have h1 : Y ≤ X := by rwa [min_eq_left hA.le] at hge
  have h2 : X ≤ Y := by
    rcases le_total X M with h | h
    · rwa [min_eq_left h] at hle
    · rw [min_eq_right h] at hle; exact absurd (lt_of_le_of_lt hle hA) (lt_irrefl _)
  exact le_antisymm h2 h1

theorem nval_pow_p (T : CDVR) (p e : ℕ) (he : 0 < e) (hp : vV T.V (p : T.Fr) = e) (N : ℕ) :
    nval T.V e ((p : T.Fr) ^ N) = ((N : ℝ) : EReal) := by
  have hp0 : (p : T.Fr) ≠ 0 := by
    intro h0
    rw [h0] at hp
    simp [vV] at hp
    omega
  have h1 : nval T.V e (p : T.Fr) = ((1 : ℝ) : EReal) := by
    rw [nval_of_ne hp0, hp]
    congr 1
    have : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
    push_cast
    field_simp
  induction N with
  | zero =>
    rw [pow_zero, nval_of_ne one_ne_zero]
    simp [vV]
  | succ N ih =>
    rw [pow_succ, nval_mul, ih, h1, ← EReal.coe_add]
    push_cast
    rfl

end GlobalTheory.PertDepth

open GlobalTheory.PertDepth in

theorem GlobalTheory.nuLocOf_pert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (e : ℕ), 0 < e → vV T.V (p : T.Fr) = e → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n N k : ℕ) (ρ B : ℝ) (P₀ R : MvPolynomial (LtN Dw n) T.Fr), ChBound Ch e ρ a n → R ∈ FFV (Dw := Dw) T a n → nuLocOf Ch e k P₀ ≤ (B : EReal) → B + ρ < N → nuLocOf Ch e k (P₀ + ((p : T.Fr) ^ N) • R) = nuLocOf Ch e k P₀ := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p T io y Ch e he hp a n N k ρ B P₀ R hCh hR hP₀ hBN
  letI := io.toAlgebra
  have hRv : ∀ f : PS T.Fr n Ch.ch.d, IsIntPS T f →
      ((-ρ : ℝ) : EReal) ≤ nval T.V e (nabValN Ch.ch.B T.Fr Ch.ch.h H.w0 k f (fun ℓ => ℓ.2.2)
        (fun ℓ => Ch.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) R) := by
    intro f hf
    have h1 := hCh k
    rw [nuLocC_eq_iInf] at h1
    exact le_trans h1 (le_trans (iInf₂_le R hR) (iInf₂_le f hf))
  unfold nuLocOf
  simp only [Formalism.MainNotions.ModuliIntegralCharts.H1.DescentPf.nabValN_addP, Formalism.MainNotions.ModuliIntegralCharts.H1.DescentPf.nabValN_smulP]
  refine iInf_nval_add_eq T e _ _ _ (((N : ℝ) - ρ : ℝ) : EReal) (fun f hf => ?_) ?_
  · rw [nval_mul, nval_pow_p T p e he hp N]
    have := add_le_add (le_refl ((N : ℝ) : EReal)) (hRv f hf)
    rw [← EReal.coe_add] at this
    simpa [sub_eq_add_neg] using this
  · refine lt_of_le_of_lt hP₀ ?_
    exact EReal.coe_lt_coe_iff.2 (by linarith)
end

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localDepth_stable_under_prime_pow_perturbation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (e : ℕ), 0 < e → vV T.V (p : T.Fr) = e → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n N k : ℕ) (ρ B : ℝ) (P₀ R : MvPolynomial (LtN Dw n) T.Fr), ChBound Ch e ρ a n → R ∈ FFV (Dw := Dw) T a n → nuLocOf Ch e k P₀ ≤ (B : EReal) → B + ρ < N → nuLocOf Ch e k (P₀ + ((p : T.Fr) ^ N) • R) = nuLocOf Ch e k P₀ := by
  atlas_forward_decl GlobalTheory.nuLocOf_pert
end

section
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RefSum.GlobalPoly

theorem vLa_pos_of_mem {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {p : ℕ} (hp0 : p ≠ 0)
    (hp : (p : 𝓞 K) ∈ v.asIdeal) : 0 < vLa v (p : K) := by
  have hne : (p : K) ≠ 0 := by exact_mod_cast hp0
  have hlt : v.valuation K (p : K) < 1 := by
    rw [← map_natCast (algebraMap (𝓞 K) K) p, HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hp
  have h0 : v.valuation K (p : K) ≠ 0 := by simpa using hne
  have := (WithZero.log_lt_log h0 one_ne_zero).2 hlt
  simp only [WithZero.log_one] at this
  simp only [vLa]; omega

theorem vV_of_isUnit (T : CDVR) {x : T.V} (hx : IsUnit x) : vV T.V (algebraMap T.V T.Fr x) = 0 := by
  have : valV T.V (algebraMap T.V T.Fr x) = 1 := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h hx
  simp [vV, this]

theorem vV_prime_le (T : CDVR) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hv : 0 < vV T.V (p : T.Fr)) :
    vV T.V (q : T.Fr) ≤ vV T.V (p : T.Fr) := by
  by_cases hpq : q = p
  · subst hpq; exact le_rfl
  have hcop : IsCoprime ((q : ℤ)) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hp).2 hpq)
  have hcopV : IsCoprime ((q : T.V)) (p : T.V) := by
    simpa using hcop.map (Int.castRingHom T.V)
  have hpm : (p : T.V) ∈ IsLocalRing.maximalIdeal T.V := by
    by_contra h
    have hu : IsUnit (p : T.V) := by
      by_contra h'; exact h ((IsLocalRing.mem_maximalIdeal _).2 h')
    have := vV_of_isUnit T hu
    rw [map_natCast] at this; omega
  have hqu : IsUnit (q : T.V) := by
    by_contra h'
    have hqm : (q : T.V) ∈ IsLocalRing.maximalIdeal T.V := (IsLocalRing.mem_maximalIdeal _).2 h'
    obtain ⟨u, w, huw⟩ := hcopV
    have h1 : (1 : T.V) ∈ IsLocalRing.maximalIdeal T.V := by
      rw [← huw]; exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hqm) (Ideal.mul_mem_left _ _ hpm)
    exact (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have := vV_of_isUnit T hqu
  rw [map_natCast] at this
  rw [this]; exact hv.le

end GlobalTheory.RefSum.GlobalPoly

theorem GlobalTheory.RefSum.GlobalPoly.exists_polyBetween : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (a : (D.host.E →+* ℂ) × ℕ → ℕ), (∀ τ, Antitone fun i => a (τ, i)) → ∀ n : ℕ, ∑ f : Lt1 Dw, 2 * rk f ≤ n → ∀ A B : ℝ, NuBetween Xo la (gap Dw a) A B → ∃ P₁ ∈ harmA (Dw := Dw) c a n, PolyBetween Xo la P₁ A B := by
  intro D H Dw l Xo c
  letI := H.starRing
  intro p hp la a ha n hn A B hNu
  obtain ⟨N, hN⟩ := exists_nat_gt (B + ∑ q ∈ D.host.condN.primeFactors,
    1 * D.host.vdH q * ((Formalism.L2.Pj.DF Dw a : ℕ) : ℝ) / 2)
  obtain ⟨P₁, hP₁, hglob⟩ := GlobalTheory.T.exists_global_harmonic_congr_column_polynomial D.host.E H Dw l Xo c p la a ha n hn N
  refine ⟨P₁, hP₁, fun T io e ho y hy Ch k => ?_⟩
  obtain ⟨Bc, R, hcols, hR, heq⟩ := hglob T io e ho
  have hchoice := GlobalTheory.T.columnPolynomial_localDepth_eq_placeDepth D.host.E H Dw l Xo c p la T io e ho y Ch (gap Dw a) n Bc hcols k
  have hv : 0 < vV T.V (p : T.Fr) := by
    rw [← map_natCast io p, ho.2]
    exact mul_pos (by exact_mod_cast ho.1) (GlobalTheory.RefSum.GlobalPoly.vLa_pos_of_mem la.1 hp.out.ne_zero la.2)
  have hve : vV T.V (p : T.Fr) = ((vV T.V (p : T.Fr)).toNat : ℤ) := (Int.toNat_of_nonneg hv.le).symm
  have he : 0 < (vV T.V (p : T.Fr)).toNat := by omega
  have hch := GlobalTheory.PlaceInt.HostChart.chBound_host D H Dw l Xo c (fun _ => rfl) T io y Ch _ he a n
    (Formalism.L2.Pj.DF Dw a) le_rfl
  have hNu' := hNu T io e ho y
  have hpert := GlobalTheory.T.localDepth_stable_under_prime_pow_perturbation D.host.E H Dw l Xo c p T io y Ch _ he hve a n N k _ B (polyT Bc (gap Dw a)) R hch hR
    (hchoice.trans_le (hNu'.2 hy)) (by
      refine lt_of_le_of_lt (add_le_add le_rfl (Finset.sum_le_sum fun q hq => ?_)) hN
      have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
      have hle := GlobalTheory.RefSum.GlobalPoly.vV_prime_le T hp.out hqp hv
      have hr : (vV T.V (q : T.Fr) : ℝ) / ((vV T.V (p : T.Fr)).toNat : ℝ) ≤ 1 := by
        rw [div_le_one (by exact_mod_cast he)]
        rw [hve] at hle
        exact_mod_cast hle
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hr (D.host.vdH_nonneg q)) (Nat.cast_nonneg _)) zero_le_two)
  rw [heq, hpert, hchoice]
  exact ⟨hNu'.1, hNu'.2 hy⟩
end

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harmonicPolynomial_localDepth_between : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (a : (D.host.E →+* ℂ) × ℕ → ℕ), (∀ τ, Antitone fun i => a (τ, i)) → ∀ n : ℕ, ∑ f : Lt1 Dw, 2 * rk f ≤ n → ∀ A B : ℝ, NuBetween Xo la (gap Dw a) A B → ∃ P₁ ∈ harmA (Dw := Dw) c a n, PolyBetween Xo la P₁ A B := by
  atlas_forward_decl GlobalTheory.RefSum.GlobalPoly.exists_polyBetween
end
