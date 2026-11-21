import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiHolomorphicNearPositiveMatricesAtOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KTypeExtendsHolomorphicComplexifiedK
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivedAdjoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlWordJetRelationsEqZeroOfNil
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryFlowCoeffEqOfTaylorSeries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlWordJetRelationsOfSchmidSystemJets
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeFunctionEquivalence
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsoPartStable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerKTypesPTensorStableUnderK
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdPartialZpow
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsURepOnOfIsTau
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhiPositiveDefiniteCholeskyFormula
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

section
section
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.SphJet.ModRel

theorem ew_append {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V)
    (l₁ l₂ : List (Fin n × Fin n)) : ew E (l₁ ++ l₂) = ew E l₁ * ew E l₂ := by
  induction l₁ with
  | nil => simp [ew]
  | cons p w ih => simp only [List.cons_append, ew, ih, mul_assoc]

theorem thetaA_one_onePositionArrayOfIsometry {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (j : W →ₗᵢ[ℂ] V)
    (G : Fin n × Fin n → W) : thetaA E 1 (arr1 j G) = ∑ p : Fin n × Fin n, E p.1 p.2 (j (G p)) := by
  rw [theta_map_word_sum_apply]
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n × Fin n)) _ _ fun α => ?_
  simp [ew, arr1, arrTo]

theorem theta_vminus {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ} {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ V} {Λ : Fin n → ℝ} {u : V} (hg : GlRel E)
    (h0 : ∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ x : V, KHighest ε E (Λ - root a b) x → x = 0) :
    Vminus ε E Λ u ≤ LinearMap.ker (thetaA E 1) := by
  obtain ⟨-, hθ⟩ := (arrModule V n ε E 1).1 hg
  apply isotypic_part_le_of_forall
  intro y hy μ hμ hyh
  apply compact_span_le_of_stable
  · intro c d _ x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hθ, hx, map_zero]
  · rw [LinearMap.mem_ker]
    obtain ⟨a, b, hba, hne, rfl⟩ := hμ
    have hμeq : Λ + root a b = Λ - root b a := by
      rw [root_swap' a b, sub_eq_add_neg]
    refine h0 b a hba (Ne.symm hne) _ ⟨fun c => ?_, fun c d hcd hcomp => ?_⟩
    · rw [← hθ, hyh.1 c, map_smul, hμeq]
    · rw [← hθ, hyh.2 c d hcd hcomp, map_zero]

theorem modJet_jetRel (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ)
    (u : V) (j : W →ₗᵢ[ℂ] V) (hL : LowData ε E Λ u j)
    (h0 : ∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ x : V, KHighest ε E (Λ - root a b) x → x = 0) :
    JetRel ε E Λ u j (modJet E j) := by
  obtain ⟨hg, hu, -, -, -⟩ := hL
  refine ⟨fun l₁ l₂ a b c d => ?_, fun l a b _ y x x' hx => ?_, fun l a b hab y y' x hy => ?_,
    fun l G hG y => ?_⟩
  · have key : ew E (l₁ ++ (a, b) :: (c, d) :: l₂) - ew E (l₁ ++ (c, d) :: (a, b) :: l₂) =
        (if b = c then ew E (l₁ ++ (a, d) :: l₂) else 0) - (if d = a then ew E (l₁ ++ (c, b) :: l₂) else 0) := by
      have h := hg a b c d
      simp only [ew_append, ew]
      rw [← mul_sub, ← mul_assoc (E a b), ← mul_assoc (E c d), ← sub_mul, h]
      split_ifs <;> simp [mul_sub, sub_mul]
    ext y x
    have h2 := congrArg (fun T : Module.End ℂ V => ⟪j y, T (j x)⟫_ℂ) key
    split_ifs at h2 ⊢ <;>
      simpa [modJet_apply, inner_sub_right] using h2
  · simp only [modJet_apply, ew_append, ew, hx, mul_one, Module.End.mul_apply]
  · simp only [modJet_apply, ew, hy, Module.End.mul_apply]
    rw [isUnitary_kUnit ε E hu b a hab.symm]
  · have h := theta_vminus hg h0 hG
    rw [LinearMap.mem_ker, thetaA_one_onePositionArrayOfIsometry] at h
    simp only [modJet_apply, ew_append, ew, mul_one, Module.End.mul_apply]
    rw [← inner_sum, ← map_sum, h, map_zero, inner_zero_right]

end GlobalTheory.SphJet.ModRel
end
end

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compressedWords_glWordJetRelations_of_no_types : ∀ (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) (j : W →ₗᵢ[ℂ] V), LowData ε E Λ u j → (∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ x : V, KHighest ε E (Λ - root a b) x → x = 0) → JetRel ε E Λ u j (modJet E j) := by
  atlas_forward_decl GlobalTheory.SphJet.ModRel.modJet_jetRel
end

section
section
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.SphJet.Taylor

variable {n : ℕ}

theorem analyticAt_Rz {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    {f : Matrix (Fin n) (Fin n) ℂ → B} (hf : AnalyticAt ℂ f 1) (Z : Matrix (Fin n) (Fin n) ℂ) :
    AnalyticAt ℂ (Rz Z f) 1 := by
  unfold Rz
  exact (ContinuousLinearMap.id ℂ (Matrix (Fin n) (Fin n) ℂ →L[ℂ] B)).analyticAt_bilinear _ |>.comp₂ hf.fderiv
    (analyticAt_id.mul analyticAt_const)

theorem analyticAt_Rw {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (ε : Fin n → Bool)
    {f : Matrix (Fin n) (Fin n) ℂ → B} (hf : AnalyticAt ℂ f 1) (l : List (Fin n × Fin n)) :
    AnalyticAt ℂ (Rw ε l f) 1 := by
  induction l with
  | nil => exact hf
  | cons p l ih => exact analyticAt_Rz ih _

theorem hasDerivAt_expC (Z : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    HasDerivAt (fun t : ℂ => NormedSpace.exp (t • Z)) (NormedSpace.exp (s • Z) * Z) s :=
  hasDerivAt_exp_smul_const Z s

theorem analyticAt_expC (Z : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    AnalyticAt ℂ (fun t : ℂ => NormedSpace.exp (t • Z)) s :=
  Differentiable.analyticAt (fun t => (hasDerivAt_expC Z t).differentiableAt) s

theorem analyticAt_comp {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    {g : Matrix (Fin n) (Fin n) ℂ → B} (hg : AnalyticAt ℂ g 1) (L : B →L[ℂ] ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    AnalyticAt ℝ (fun t : ℝ => L (g (NormedSpace.exp ((t : ℂ) • Z)))) 0 := by
  have h1 : AnalyticAt ℂ (fun t : ℂ => L (g (NormedSpace.exp (t • Z)))) 0 :=
    (L.analyticAt _).comp (AnalyticAt.comp_of_eq hg (analyticAt_expC Z 0) (by simp))
  have h2 := AnalyticAt.comp_of_eq (h1.restrictScalars (𝕜 := ℝ)) (Complex.ofRealCLM.analyticAt 0) (by simp)
  exact h2

theorem deriv_comp_eventually {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    {g : Matrix (Fin n) (Fin n) ℂ → B} (hg : AnalyticAt ℂ g 1) (L : B →L[ℂ] ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    deriv (fun t : ℝ => L (g (NormedSpace.exp ((t : ℂ) • Z)))) =ᶠ[𝓝 0]
      fun t : ℝ => L (Rz Z g (NormedSpace.exp ((t : ℂ) • Z))) := by
  have hc : Tendsto (fun t : ℝ => NormedSpace.exp ((t : ℂ) • Z)) (𝓝 0) (𝓝 1) := by
    have : ContinuousAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • Z)) 0 :=
      (hasDerivAt_expC Z ((0 : ℝ) : ℂ)).continuousAt.comp Complex.continuous_ofReal.continuousAt
    simpa [ContinuousAt] using this
  filter_upwards [hc.eventually hg.eventually_analyticAt] with t ht
  have h1 : HasDerivAt (fun s : ℂ => L (g (NormedSpace.exp (s • Z))))
      (L (Rz Z g (NormedSpace.exp ((t : ℂ) • Z)))) (t : ℂ) :=
    L.hasFDerivAt.comp_hasDerivAt _ (ht.differentiableAt.hasFDerivAt.comp_hasDerivAt _ (hasDerivAt_expC Z t))
  exact h1.comp_ofReal.deriv

theorem Rz_thM {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] (ε : Fin n → Bool)
    (X : Matrix (Fin n) (Fin n) ℂ) (g : Matrix (Fin n) (Fin n) ℂ → B) (z : Matrix (Fin n) (Fin n) ℂ) :
    Rz (thM ε X) g z = ∑ p : Fin n × Fin n, X p.1 p.2 • Rz (thE ε p) g z := by
  simp only [Rz, thM, Finset.mul_sum, map_sum, mul_smul_comm, map_smul]

theorem iteratedDeriv_inner_exp : ∀ (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) [CompleteSpace W] (j : W →ₗᵢ[ℂ] V) (f : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)), AnalyticAt ℂ f 1 → (∀ l, funJet ε f l = modJet E j l) → ∀ (X : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) (y x : W), iteratedDeriv m (fun t : ℝ => ⟪y, f (NormedSpace.exp ((t : ℂ) • thM ε X)) x⟫_ℂ) 0 = ⟪j y, (actM E X ^ m) (j x)⟫_ℂ := by
  intro V W _ _ _ _ n ε E _ j f hf hJ X m y x
  let L : (W →L[ℂ] W) →L[ℂ] ℂ := (innerSL ℂ y).comp (ContinuousLinearMap.apply ℂ W x)
  have hL : ∀ T : W →L[ℂ] W, L T = ⟪y, T x⟫_ℂ := fun T => rfl
  have key : ∀ (m : ℕ) (l : List (Fin n × Fin n)),
      iteratedDeriv m (fun t : ℝ => L (Rw ε l f (NormedSpace.exp ((t : ℂ) • thM ε X)))) 0 =
        ⟪j y, (actM E X ^ m) (ew E l (j x))⟫_ℂ := by
    intro m
    induction m with
    | zero =>
      intro l
      have := congrArg (fun B => B y x) (hJ l)
      simp only [funJet_apply, modJet_apply] at this
      simpa [hL] using this
    | succ m ih =>
      intro l
      rw [iteratedDeriv_succ', (deriv_comp_eventually (analyticAt_Rw ε hf l) L _).iteratedDeriv_eq]
      have e : (fun t : ℝ => L (Rz (thM ε X) (Rw ε l f) (NormedSpace.exp ((t : ℂ) • thM ε X)))) =
          fun t : ℝ => ∑ p : Fin n × Fin n,
            X p.1 p.2 * L (Rw ε (p :: l) f (NormedSpace.exp ((t : ℂ) • thM ε X))) := by
        funext t
        rw [Rz_thM, map_sum]
        simp only [map_smul, smul_eq_mul]
        rfl
      rw [e, iteratedDeriv_fun_sum (fun p _ =>
        contDiffAt_const.mul (analyticAt_comp (analyticAt_Rw ε hf (p :: l)) L _).contDiffAt)]
      have e2 : ∀ p : Fin n × Fin n, iteratedDeriv m (fun t : ℝ =>
            X p.1 p.2 * L (Rw ε (p :: l) f (NormedSpace.exp ((t : ℂ) • thM ε X)))) 0 =
          X p.1 p.2 * ⟪j y, (actM E X ^ m) (E p.1 p.2 (ew E l (j x)))⟫_ℂ := by
        intro p
        rw [iteratedDeriv_const_mul _ (analyticAt_comp (analyticAt_Rw ε hf (p :: l)) L _).contDiffAt, ih]
        simp [ew]
      simp only [e2]
      rw [pow_succ, Module.End.mul_apply]
      have e3 : ∀ v : V, actM E X v = ∑ p : Fin n × Fin n, X p.1 p.2 • E p.1 p.2 v := by
        intro v
        simp [actM, Fintype.sum_prod_type, LinearMap.sum_apply]
      rw [e3, map_sum, inner_sum]
      simp only [map_smul, inner_smul_right]
  simpa [hL, Rw, ew] using key m []

end GlobalTheory.SphJet.Taylor
end
end

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedDeriv_inner_exp_eq_wordJetForms : ∀ (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) [CompleteSpace W] (j : W →ₗᵢ[ℂ] V) (f : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)), AnalyticAt ℂ f 1 → (∀ l, funJet ε f l = modJet E j l) → ∀ (X : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) (y x : W), iteratedDeriv m (fun t : ℝ => ⟪y, f (NormedSpace.exp ((t : ℂ) • thM ε X)) x⟫_ℂ) 0 = ⟪j y, (actM E X ^ m) (j x)⟫_ℂ := by
  atlas_forward_decl GlobalTheory.SphJet.Taylor.iteratedDeriv_inner_exp
end

section
section
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.SphJet

theorem vminus_coef : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V), GlRel E → IsUnitary ε E → KHighest ε E Λ u → ∀ F ∈ Vminus ε E Λ u, ∀ a b : Fin n, a ≤ b → ⟪u, arrOf V n 1 F (fun _ => (a, b))⟫_ℂ = 0 := by
  intro V _ _ n ε E Λ u hg hu hΛ F hF a b hab
  have hkr : KRel ε (arrE E 1) := glRel_kRel ε _ ((arrModule V n ε E 1).1 hg).1
  have hku : KUnit ε E := isUnitary_kUnit ε E hu

  let φ : Arr V n 1 →ₗ[ℂ] ℂ :=
    (innerₛₗ ℂ u).comp ((LinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 → Fin n × Fin n => V)
      (fun _ => (a, b))).comp (arrOf V n 1))
  suffices hle : Vminus ε E Λ u ≤ LinearMap.ker φ by
    have h0 : φ F = 0 := hle hF
    simpa [φ] using h0

  refine iSup₂_le fun y hy => ?_
  obtain ⟨-, μ, ⟨c, d, hdc, -, rfl⟩, hyh⟩ := hy
  rw [(kLow _ n ε (arrE E 1) _ y hkr hyh).1]
  refine Submodule.span_le.2 ?_
  rintro z ⟨w, hw, rfl⟩

  obtain ⟨ν, hht, hν⟩ := GlobalTheory.Jet.VminusComp.word_weight hkr hyh.1 w hw
  have hcw := GlobalTheory.Jet.VminusComp.comp_weight hν a b
  have hne : Λ ≠ ν - root a b := by
    intro h
    have h1 := congrArg GlobalTheory.Jet.VminusComp.ht h
    rw [GlobalTheory.Jet.VminusComp.ht_sub, GlobalTheory.Jet.VminusComp.ht_root] at h1
    rw [GlobalTheory.Jet.VminusComp.ht_add, GlobalTheory.Jet.VminusComp.ht_root] at hht
    have h2 : ((d : ℕ) : ℝ) < ((c : ℕ) : ℝ) := by exact_mod_cast hdc
    have h3 : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
    linarith

  have h0 := kWtOrth V n ε E Λ (ν - root a b) u _ hku hΛ.1 hcw hne
  simpa [φ, arrOf] using h0

end GlobalTheory.SphJet
end
end

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.negativeRootArray_highestVector_coeff_eq_zero : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V), GlRel E → IsUnitary ε E → KHighest ε E Λ u → ∀ F ∈ Vminus ε E Λ u, ∀ a b : Fin n, a ≤ b → ⟪u, arrOf V n 1 F (fun _ => (a, b))⟫_ℂ = 0 := by
  atlas_forward_decl GlobalTheory.SphJet.vminus_coef
end

section
section
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

namespace GlobalTheory.PhiUpperDeriv

theorem differentiableAt_prod {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : Finset ι)
    {f : ι → E → ℂ} {z : E} (h : ∀ i, DifferentiableAt ℂ (f i) z) :
    DifferentiableAt ℂ (fun y => ∏ i ∈ s, f i y) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact differentiableAt_const _
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a).mul ih

theorem differentiableAt_leadMinor {n : ℕ} (l : ℕ) (hl : l ≤ n) (z : Matrix (Fin n) (Fin n) ℂ) :
    DifferentiableAt ℂ (fun y : Matrix (Fin n) (Fin n) ℂ => leadMinor y l hl) z := by
  have hent : ∀ a b : Fin n, DifferentiableAt ℂ (fun y : Matrix (Fin n) (Fin n) ℂ => y a b) z := by
    intro a b
    let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
      { toFun := fun y => y a b
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact (LinearMap.toContinuousLinearMap L).differentiableAt
  have hexp : (fun y : Matrix (Fin n) (Fin n) ℂ => leadMinor y l hl) = fun y =>
      ∑ σ : Equiv.Perm (Fin l), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ i : Fin l, y (Fin.castLE hl (σ i)) (Fin.castLE hl i) := by
    funext y
    simp only [leadMinor, Matrix.det_apply', Matrix.submatrix_apply]
  rw [hexp]
  have key : ∀ σ : Equiv.Perm (Fin l), DifferentiableAt ℂ (fun y : Matrix (Fin n) (Fin n) ℂ =>
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i : Fin l, y (Fin.castLE hl (σ i)) (Fin.castLE hl i)) z :=
    fun σ => (differentiableAt_prod Finset.univ fun i => hent _ _).const_mul _
  have hsum := DifferentiableAt.sum (u := Finset.univ) fun σ _ => key σ
  rw [Finset.sum_fn] at hsum
  exact hsum

theorem differentiableAt_Phi {n : ℕ} (lam : Fin n → ℝ) {y : Matrix (Fin n) (Fin n) ℂ} (hy : y ∈ Omega n) :
    DifferentiableAt ℂ (Phi lam) y := by
  have hPhi : Phi lam = fun z => ∏ i : Fin n, leadMinor z (i.val + 1) i.isLt ^ (-(sInt lam i)) :=
    funext fun _ => rfl
  rw [hPhi]
  refine differentiableAt_prod Finset.univ fun i => ?_
  exact (differentiableAt_leadMinor (i.val + 1) i.isLt y).zpow (Or.inl (hy i))

theorem Phi_mul_unipotent {n : ℕ} (lam : Fin n → ℝ) {y N : Matrix (Fin n) (Fin n) ℂ} (hy : y ∈ Omega n)
    (hN : ∀ i i' : Fin n, i' ≤ i → N i i' = 0) (t : ℂ) : Phi lam (y + t • (y * N)) = Phi lam y := by
  have hline : y + t • (y * N) = 1 * y * (1 + t • N) := by
    rw [Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
  have hlo : IsLo (1 : Matrix (Fin n) (Fin n) ℂ) := fun i j hij =>
    Matrix.one_apply_ne (ne_of_lt hij)
  have hup : IsUp (1 + t • N) := fun i j hji => by
    rw [Matrix.add_apply, Matrix.smul_apply, hN i j hji.le, Matrix.one_apply_ne (ne_of_gt hji)]
    simp
  have hdiag : ∀ l, (1 : Matrix (Fin n) (Fin n) ℂ) l l ≠ 0 ∧ (1 + t • N) l l ≠ 0 := fun l => by
    rw [Matrix.add_apply, Matrix.smul_apply, hN l l le_rfl, Matrix.one_apply_eq]
    simp
  obtain ⟨-, hval⟩ := GlobalTheory.PhiTriangular.phiTri n lam 1 y (1 + t • N) hlo hup hdiag hy
  rw [hline, hval]
  have hone : ∀ l, ((1 : Matrix (Fin n) (Fin n) ℂ) l l * (1 + t • N) l l) = 1 := fun l => by
    rw [Matrix.add_apply, Matrix.smul_apply, hN l l le_rfl, Matrix.one_apply_eq]
    simp
  simp only [hone, _root_.one_zpow, Finset.prod_const_one, one_mul]

theorem fderiv_Phi_upper : ∀ (n : ℕ) (lam : Fin n → ℝ) (y N : Matrix (Fin n) (Fin n) ℂ), y ∈ Omega n →
    (∀ i i' : Fin n, i' ≤ i → N i i' = 0) → fderiv ℂ (Phi lam) y (y * N) = 0 := by
  intro n lam y N hy hN
  have hD : HasFDerivAt (Phi lam) (fderiv ℂ (Phi lam) y) y := (differentiableAt_Phi lam hy).hasFDerivAt
  have hL : HasDerivAt (fun t : ℂ => y + t • (y * N)) (y * N) 0 := by
    have h1 := ((hasDerivAt_id (0 : ℂ)).smul_const (y * N)).const_add y
    simpa only [one_smul, id] using h1
  have hcomp : HasDerivAt (fun t : ℂ => Phi lam (y + t • (y * N))) (fderiv ℂ (Phi lam) y (y * N)) 0 :=
    hD.comp_hasDerivAt_of_eq (0 : ℂ) hL (by simp)
  have hconst : (fun t : ℂ => Phi lam (y + t • (y * N))) = fun _ => Phi lam y :=
    funext fun t => Phi_mul_unipotent lam hy hN t
  rw [hconst] at hcomp
  exact hcomp.unique (hasDerivAt_const 0 (Phi lam y))

end GlobalTheory.PhiUpperDeriv
end

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fderiv_leadingMinorPowerProduct_strictUpper_eq_zero : ∀ (n : ℕ) (lam : Fin n → ℝ) (y N : Matrix (Fin n) (Fin n) ℂ), y ∈ Omega n → (∀ i i' : Fin n, i' ≤ i → N i i' = 0) → fderiv ℂ (Phi lam) y (y * N) = 0 := by
  atlas_forward_decl GlobalTheory.PhiUpperDeriv.fderiv_Phi_upper
end

section
section
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.SphJet.PsDer

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private lemma aestronglyMeasurable_of_continuous_compact {K E : Type*} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K]
    [OpensMeasurableSpace K] [NormedAddCommGroup E] (μ : Measure K) {f : K → E} (hf : Continuous f) :
    AEStronglyMeasurable f μ := by
  have h := hf.continuousOn.aestronglyMeasurable_of_isCompact (μ := μ) isCompact_univ MeasurableSet.univ
  rwa [Measure.restrict_univ] at h

private lemma integrable_of_continuous_compact' {K E : Type*} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [OpensMeasurableSpace K] [NormedAddCommGroup E] (μ : Measure K) [IsFiniteMeasure μ]
    {f : K → E} (hf : Continuous f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound (aestronglyMeasurable_of_continuous_compact μ hf) C
    (Filter.Eventually.of_forall fun k => hC k (Set.mem_univ k))

theorem hasDerivAt_integral_cpt {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K]
    [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] {F F' : ℂ → K → ℂ} {s : Set ℂ} (hs : s ∈ 𝓝 (0 : ℂ))
    (hF : ∀ t ∈ s, Continuous (F t)) (hF' : ContinuousOn (fun x : ℂ × K => F' x.1 x.2) (s ×ˢ Set.univ))
    (hd : ∀ k, ∀ t ∈ s, HasDerivAt (F · k) (F' t k) t) :
    HasDerivAt (fun t => ∫ k, F t k ∂μ) (∫ k, F' 0 k ∂μ) 0 := by
  have h0 : (0 : ℂ) ∈ s := mem_of_mem_nhds hs
  obtain ⟨r, hr, hrs⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hs
  have hcpt : IsCompact (Metric.closedBall (0 : ℂ) r ×ˢ (Set.univ : Set K)) :=
    (isCompact_closedBall 0 r).prod isCompact_univ
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn (hF'.mono (Set.prod_mono hrs subset_rfl))
  have hF'0 : Continuous (F' 0) :=
    hF'.comp_continuous (continuous_const.prodMk continuous_id) fun k => ⟨h0, Set.mem_univ k⟩
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => C)
    (Metric.closedBall_mem_nhds 0 hr) ?_ (integrable_of_continuous_compact' μ (hF 0 h0))
    (aestronglyMeasurable_of_continuous_compact μ hF'0) ?_ (integrable_const C) ?_).2
  · exact Filter.eventually_of_mem hs fun t ht => aestronglyMeasurable_of_continuous_compact μ (hF t ht)
  · exact Filter.Eventually.of_forall fun k t ht => hC (t, k) ⟨ht, Set.mem_univ k⟩
  · exact Filter.Eventually.of_forall fun k t ht => hd k t (hrs ht)

private lemma analyticAt_leadMinor' (z₀ : Matrix (Fin n) (Fin n) ℂ) (l : ℕ) (hl : l ≤ n) :
    AnalyticAt ℂ (fun z : Matrix (Fin n) (Fin n) ℂ => leadMinor z l hl) z₀ := by
  have he : ∀ a b : Fin n, AnalyticAt ℂ (fun z : Matrix (Fin n) (Fin n) ℂ => z a b) z₀ := fun a b =>
    (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ a b)).analyticAt z₀
  simp only [leadMinor, Matrix.det_apply, Matrix.submatrix_apply, Units.smul_def, zsmul_eq_mul]
  refine Finset.analyticAt_fun_sum _ fun σ _ => ?_
  refine AnalyticAt.mul ?_ ?_
  · exact analyticAt_const
  · exact Finset.analyticAt_fun_prod _ fun i _ => he _ _

theorem analyticOnNhd_Phi (lam : Fin n → ℝ) : AnalyticOnNhd ℂ (Phi lam) (Omega n) := by
  intro z hz
  have hz' : ∀ i : Fin n, leadMinor z (i.val + 1) i.isLt ≠ 0 := hz
  show AnalyticAt ℂ (fun y => ∏ i : Fin n, leadMinor y (i.val + 1) i.isLt ^ (-(sInt lam i))) z
  exact Finset.analyticAt_fun_prod _ fun i _ => (analyticAt_leadMinor' z _ _).fun_zpow (hz' i)

theorem continuous_conj {ε : Fin n → Bool} {X : Type} [TopologicalSpace X] {f : X → KG ε}
    {g : X → Matrix (Fin n) (Fin n) ℂ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun p => (toMK (f p))⁻¹ * g p * toMK (f p)) := by
  have hK : Continuous (fun k : KG ε => toMK k) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hinv : ∀ k : KG ε, (toMK k)⁻¹ = toMK k⁻¹ := fun k => by
    simp [toMK, toM, Matrix.coe_units_inv]
  have e : (fun p => (toMK (f p))⁻¹ * g p * toMK (f p)) = fun p => toMK (f p)⁻¹ * g p * toMK (f p) := by
    funext p; rw [hinv]
  rw [e]
  exact ((hK.comp hf.inv).matrix_mul hg).matrix_mul (hK.comp hf)

private lemma toMK_inv_mul_mul_toMK_mem_Omega {ε : Fin n → Bool} {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ U1 ε)
    (k : KG ε) : (toMK k)⁻¹ * z * toMK k ∈ Omega n :=
  hz _ ((mem_KG ε _).1 k.2)

private lemma continuous_toMK_inv_mul_mul_toMK {ε : Fin n → Bool} (M : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun k : KG ε => (toMK k)⁻¹ * M * toMK k) :=
  continuous_conj (f := fun k => k) (g := fun _ => M) continuous_id continuous_const

private lemma continuous_inner_tau_toMK {ε : Fin n → Bool} {abelian₂ : Fin n → ℝ} {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {w : W} (h : IsTau ε abelian₂ τ w)
    (u v : W) : Continuous (fun k : KG ε => ⟪u, τ (toMK k) v⟫_ℂ) := by
  have hK : Continuous (fun k : KG ε => toMK k) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hd := h.2.2.1 u v
  exact hd.continuousOn.comp_continuous hK fun k =>
    ⟨((k : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ).isUnit, ((mem_KG ε _).1 k.2).2⟩

private lemma continuous_tau_toMK_apply {ε : Fin n → Bool} {abelian₂ : Fin n → ℝ} {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {w : W} (h : IsTau ε abelian₂ τ w)
    (v : W) : Continuous (fun k : KG ε => τ (toMK k) v) := by
  haveI : FiniteDimensional ℂ W := h.1
  let b := stdOrthonormalBasis ℂ W
  have e : (fun k : KG ε => τ (toMK k) v) = fun k => ∑ i, ⟪b i, τ (toMK k) v⟫_ℂ • b i := by
    funext k; exact (b.sum_repr' _).symm
  rw [e]
  exact continuous_finset_sum _ fun i _ => (continuous_inner_tau_toMK h (b i) v).smul continuous_const

private lemma continuous_Phi_conj_toMK {ε : Fin n → Bool} (lam : Fin n → ℝ) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : z ∈ U1 ε) : Continuous (fun k : KG ε => Phi lam ((toMK k)⁻¹ * z * toMK k)) :=
  continuous_iff_continuousAt.2 fun k =>
    ContinuousAt.comp (g := Phi lam) (f := fun k : KG ε => (toMK k)⁻¹ * z * toMK k)
      (analyticOnNhd_Phi lam _ (toMK_inv_mul_mul_toMK_mem_Omega hz k)).continuousAt (continuous_toMK_inv_mul_mul_toMK z).continuousAt

theorem inner_ps_eq {ε : Fin n → Bool} (lam : Fin n → ℝ) {abelian₂ : Fin n → ℝ} {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {w : W} (h : IsTau ε abelian₂ τ w)
    {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ U1 ε) (y u : W) :
    ⟪y, ps ε lam τ w z u⟫_ℂ = (Module.finrank ℂ W : ℂ) * ∫ k : KG ε, Phi lam ((toMK k)⁻¹ * z * toMK k) *
      (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, u⟫_ℂ) ∂(muK ε) := by
  haveI : FiniteDimensional ℂ W := h.1
  have hv : Continuous (fun k : KG ε => τ (toMK k) w) := continuous_tau_toMK_apply h w
  have hR : Continuous (fun k : KG ε => (innerSL ℂ (τ (toMK k) w)).smulRight (τ (toMK k) w)) := by
    have h1 := ((ContinuousLinearMap.smulRightL ℂ W W).continuous.comp
      ((innerSL ℂ).continuous.comp hv)).clm_apply hv
    simpa using h1
  have hG : Continuous (fun k : KG ε => Phi lam ((toMK k)⁻¹ * z * toMK k) •
      (innerSL ℂ (τ (toMK k) w)).smulRight (τ (toMK k) w)) :=
    (continuous_Phi_conj_toMK lam hz).smul hR
  have hGi := integrable_of_continuous_compact' (muK ε) hG
  have hGu := hGi.apply_continuousLinearMap u
  simp only [ps]
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, ContinuousLinearMap.integral_apply hGi u,
    ← integral_inner hGu y]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    inner_smul_right]
  ring

theorem inner_fderiv_ps : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), IsHCParam lam → IsTau ε (lowK ε lam) τ w → ∀ z ∈ U1 ε, ∀ (A : Matrix (Fin n) (Fin n) ℂ) (y x : W), Integrable (fun k : KG ε => fderiv ℂ (Phi lam) ((toMK k)⁻¹ * z * toMK k) ((toMK k)⁻¹ * A * toMK k) * (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ)) (muK ε) ∧ ⟪y, fderiv ℂ (ps ε lam τ w) z A x⟫_ℂ = (Module.finrank ℂ W : ℂ) * ∫ k : KG ε, fderiv ℂ (Phi lam) ((toMK k)⁻¹ * z * toMK k) ((toMK k)⁻¹ * A * toMK k) * (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ) ∂(muK ε) := by
  intro n ε lam W _ _ τ w hHC hTau z hz A y x
  haveI : FiniteDimensional ℂ W := hTau.1
  obtain ⟨hopen, -, hdiff, -⟩ := psBasic n ε lam W τ w hHC hTau
  have hU : IsOpen (U1 ε) := hopen
  have hSn : {t : ℂ | z + t • A ∈ U1 ε} ∈ 𝓝 (0 : ℂ) := by
    have hcont : Continuous (fun t : ℂ => z + t • A) := continuous_const.add (continuous_id.smul continuous_const)
    exact hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds (by simpa using hz))
  have hpsD : DifferentiableAt ℂ (ps ε lam τ w) z := hdiff.differentiableAt (hopen.mem_nhds hz)
  have hline : HasDerivAt (fun t : ℂ => z + t • A) A 0 := by
    have h := ((hasDerivAt_id' (0 : ℂ)).smul_const A).const_add z
    rw [one_smul] at h
    exact h
  have hg1 : HasDerivAt (fun t : ℂ => ⟪y, ps ε lam τ w (z + t • A) x⟫_ℂ)
      ⟪y, fderiv ℂ (ps ε lam τ w) z A x⟫_ℂ 0 := by
    let L : (W →L[ℂ] W) →L[ℂ] ℂ := (innerSL ℂ y).comp (ContinuousLinearMap.apply ℂ W x)
    have h1 := hpsD.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hline (by simp)
    have h2 := L.hasFDerivAt.comp_hasDerivAt (0 : ℂ) h1
    have h3 := h2
    simp only [L, Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      innerSL_apply_apply] at h3
    exact h3
  have hv : Continuous (fun k : KG ε => τ (toMK k) w) := continuous_tau_toMK_apply hTau w
  have hc : Continuous (fun k : KG ε => ⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ) :=
    (continuous_const.inner hv).mul (hv.inner continuous_const)
  have hconj : Continuous (fun p : ℂ × KG ε => (toMK p.2)⁻¹ * (z + p.1 • A) * toMK p.2) :=
    continuous_conj continuous_snd (continuous_const.add (continuous_fst.smul continuous_const))
  have hmem : ∀ t ∈ {t : ℂ | z + t • A ∈ U1 ε}, ∀ k : KG ε,
      (toMK k)⁻¹ * (z + t • A) * toMK k ∈ Omega n := fun t ht k => toMK_inv_mul_mul_toMK_mem_Omega ht k
  have hAn := analyticOnNhd_Phi (n := n) lam
  have hdA := hAn.fderiv
  have hFc : ∀ t ∈ {t : ℂ | z + t • A ∈ U1 ε}, Continuous (fun k : KG ε =>
      Phi lam ((toMK k)⁻¹ * (z + t • A) * toMK k) * (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ)) :=
    fun t ht => (continuous_Phi_conj_toMK lam ht).mul hc
  have hF'c : ContinuousOn (fun p : ℂ × KG ε => fderiv ℂ (Phi lam) ((toMK p.2)⁻¹ * (z + p.1 • A) * toMK p.2)
      ((toMK p.2)⁻¹ * A * toMK p.2) * (⟪y, τ (toMK p.2) w⟫_ℂ * ⟪τ (toMK p.2) w, x⟫_ℂ))
      ({t : ℂ | z + t • A ∈ U1 ε} ×ˢ Set.univ) := by
    intro p hp
    have h1 : ContinuousAt (fun q : ℂ × KG ε =>
        fderiv ℂ (Phi lam) ((toMK q.2)⁻¹ * (z + q.1 • A) * toMK q.2)) p :=
      ContinuousAt.comp (g := fderiv ℂ (Phi lam))
        (f := fun q : ℂ × KG ε => (toMK q.2)⁻¹ * (z + q.1 • A) * toMK q.2)
        (hdA _ (hmem p.1 hp.1 p.2)).continuousAt hconj.continuousAt
    have h2 : Continuous (fun q : ℂ × KG ε => (toMK q.2)⁻¹ * A * toMK q.2) :=
      continuous_conj continuous_snd continuous_const
    exact ((h1.clm_apply h2.continuousAt).mul (hc.comp continuous_snd).continuousAt).continuousWithinAt
  have hder : ∀ k : KG ε, ∀ t ∈ {t : ℂ | z + t • A ∈ U1 ε}, HasDerivAt
      (fun s : ℂ => Phi lam ((toMK k)⁻¹ * (z + s • A) * toMK k) * (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ))
      (fderiv ℂ (Phi lam) ((toMK k)⁻¹ * (z + t • A) * toMK k) ((toMK k)⁻¹ * A * toMK k) *
        (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ)) t := by
    intro k t ht
    have hl : HasDerivAt (fun s : ℂ => (toMK k)⁻¹ * (z + s • A) * toMK k) ((toMK k)⁻¹ * A * toMK k) t := by
      have e : (fun s : ℂ => (toMK k)⁻¹ * (z + s • A) * toMK k) =
          fun s => (toMK k)⁻¹ * z * toMK k + s • ((toMK k)⁻¹ * A * toMK k) := by
        funext s; simp [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul]
      rw [e]
      have h := ((hasDerivAt_id' t).smul_const ((toMK k)⁻¹ * A * toMK k)).const_add ((toMK k)⁻¹ * z * toMK k)
      rw [one_smul] at h
      exact h
    exact ((hAn _ (hmem t ht k)).differentiableAt.hasFDerivAt.comp_hasDerivAt t hl).mul_const _
  have hD := hasDerivAt_integral_cpt (muK ε) hSn hFc hF'c hder
  have hg2 : HasDerivAt (fun t : ℂ => ⟪y, ps ε lam τ w (z + t • A) x⟫_ℂ)
      ((Module.finrank ℂ W : ℂ) * ∫ k, fderiv ℂ (Phi lam) ((toMK k)⁻¹ * (z + (0 : ℂ) • A) * toMK k)
        ((toMK k)⁻¹ * A * toMK k) * (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ) ∂(muK ε)) 0 := by
    refine (hD.const_mul _).congr_of_eventuallyEq ?_
    filter_upwards [hSn] with t ht
    exact inner_ps_eq lam hTau ht y x
  have heq := hg1.unique hg2
  simp only [zero_smul, add_zero] at heq
  refine ⟨?_, heq⟩
  have hcont0 : Continuous (fun k : KG ε => fderiv ℂ (Phi lam) ((toMK k)⁻¹ * z * toMK k)
      ((toMK k)⁻¹ * A * toMK k) * (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ)) := by
    refine continuous_iff_continuousAt.2 fun k => ContinuousAt.mul ?_ hc.continuousAt
    exact (ContinuousAt.comp (g := fderiv ℂ (Phi lam)) (f := fun k : KG ε => (toMK k)⁻¹ * z * toMK k)
      (hdA _ (toMK_inv_mul_mul_toMK_mem_Omega hz k)).continuousAt
      (continuous_toMK_inv_mul_mul_toMK z).continuousAt).clm_apply (continuous_toMK_inv_mul_mul_toMK A).continuousAt
  exact integrable_of_continuous_compact' (muK ε) hcont0

end GlobalTheory.SphJet.PsDer
end
end

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inner_fderiv_kAveragedMinorOperator_integral : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), IsHCParam lam → IsTau ε (lowK ε lam) τ w → ∀ z ∈ U1 ε, ∀ (A : Matrix (Fin n) (Fin n) ℂ) (y x : W), Integrable (fun k : KG ε => fderiv ℂ (Phi lam) ((toMK k)⁻¹ * z * toMK k) ((toMK k)⁻¹ * A * toMK k) * (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ)) (muK ε) ∧ ⟪y, fderiv ℂ (ps ε lam τ w) z A x⟫_ℂ = (Module.finrank ℂ W : ℂ) * ∫ k : KG ε, fderiv ℂ (Phi lam) ((toMK k)⁻¹ * z * toMK k) ((toMK k)⁻¹ * A * toMK k) * (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ) ∂(muK ε) := by
  atlas_forward_decl GlobalTheory.SphJet.PsDer.inner_fderiv_ps
end

section
section
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.SphJet.LowTau

theorem exp_conj {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (NormedSpace.exp A).map star = NormedSpace.exp (A.map star) := by
  have hc : ∀ B : Matrix (Fin n) (Fin n) ℂ, B.map star = Bᴴᵀ := fun B => by ext i j; simp
  rw [hc, hc, ← Matrix.exp_conjTranspose, ← Matrix.exp_transpose]

theorem inG_conj {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (h : inG ε X) :
    inG ε (X.map star) := by
  unfold inG at h ⊢
  have hJ : (Jm ε)ᵀ = Jm ε := by unfold Jm; simp
  have e1 : (X.map star)ᴴ = Xᵀ := by ext i j; simp
  have e2 : Xᴴᵀ = X.map star := by ext i j; simp
  have h2 := congrArg Matrix.transpose h
  rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, hJ, e2, Matrix.transpose_zero] at h2
  rw [e1, add_comm]
  exact h2

theorem exists_tau : ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ) (H V : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : Fin n → Fin n → Module.End ℂ V) (ι : V →ₗᵢ[ℂ] H) (u : V), IsURepOn (UJset ε) σ → DerTie ε σ E ι → ‖u‖ = 1 → IsKTypeOf ε σ Λ ((kSpan ε E u).map ι.toLinearMap) → IsWtOn (Kset ε) σ Λ (ι u) → ∃ (W : Type) (_ : NormedAddCommGroup W) (_ : InnerProductSpace ℂ W) (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W) (j : W →ₗᵢ[ℂ] V), IsTau ε Λ τ w ∧ j w = u ∧ LinearMap.range j.toLinearMap = kSpan ε E u ∧ TauTie ε E j τ := by
  intro n ε Λ H V _ _ _ _ σ E ι u hσ hD hu hK hW
  set S : Submodule ℂ H := (Formalism.REAL.kSpan ε E u).map ι.toLinearMap with hS
  have huk : u ∈ Formalism.REAL.kSpan ε E u := by
    unfold Formalism.REAL.kSpan
    exact Submodule.mem_sInf.2 fun _ h => h.1
  have huS : ι u ∈ S := Submodule.mem_map_of_mem huk
  have hKU : Formalism.REAL.Kset ε ⊆ UJset ε := by
    intro g hg
    obtain ⟨hgu, hgc⟩ := hg
    have h1 : gᴴ * g = 1 := by
      rw [← Matrix.star_eq_conjTranspose]
      exact Matrix.mem_unitaryGroup_iff'.1 hgu
    show gᴴ * Jm ε * g = Jm ε
    rw [Matrix.mul_assoc, ← hgc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hexpK : ∀ Z : Matrix (Fin n) (Fin n) ℂ, inK ε Z → NormedSpace.exp Z ∈ Formalism.REAL.Kset ε := by
    intro Z hZ
    obtain ⟨hg, hc⟩ := hZ
    unfold inG at hg
    have hZH : Zᴴ = -Z := by
      have h1 : Zᴴ * Jm ε = -(Z * Jm ε) := by
        rw [hc]; exact eq_neg_of_add_eq_zero_left hg
      calc Zᴴ = Zᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one]
        _ = -Z := by rw [h1, Matrix.neg_mul, Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one]
    refine ⟨?_, (Commute.exp_left (show Commute Z (Jm ε) from hc)).eq⟩
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hZH,
      ← Matrix.exp_add_of_commute _ _ (Commute.refl Z).neg_left, neg_add_cancel, NormedSpace.exp_zero]
  have hσK : IsURepOn (Formalism.REAL.Kset ε) σ := by
    obtain ⟨⟨h1, hm⟩, hn, hc⟩ := hσ
    exact ⟨⟨h1, fun a ha b hb => hm a (hKU ha) b (hKU hb)⟩, fun g hg => hn g (hKU hg),
      fun v => (hc v).mono hKU⟩
  have hwS : ‖(⟨ι u, huS⟩ : S)‖ = 1 := by
    show ‖(ι u : H)‖ = 1
    simp [hu]
  obtain ⟨τ, hτ, hτσ⟩ := GlobalTheory.Dec.TauExt.tauExists n ε Λ H σ S ⟨ι u, huS⟩ hσK hK hwS hW
  let e := Submodule.equivMapOfInjective ι.toLinearMap ι.injective (Formalism.REAL.kSpan ε E u)
  have heι : ∀ x : S, ι (e.symm x : V) = (x : H) := by
    intro x
    have h0 : ((e (e.symm x) : S) : H) = ι (e.symm x : V) := rfl
    rw [LinearEquiv.apply_symm_apply] at h0
    exact h0.symm
  let j : S →ₗᵢ[ℂ] V :=
    { toLinearMap := (Formalism.REAL.kSpan ε E u).subtype ∘ₗ e.symm.toLinearMap
      norm_map' := fun x => by
        show ‖(e.symm x : V)‖ = ‖x‖
        rw [← ι.norm_map, heι, Submodule.coe_norm] }
  have hjι : ∀ x : S, ι (j x) = (x : H) := heι
  refine ⟨S, inferInstance, inferInstance, τ, ⟨ι u, huS⟩, j, hτ, ι.injective (hjι _), ?_, ?_⟩
  · show LinearMap.range ((Formalism.REAL.kSpan ε E u).subtype ∘ₗ e.symm.toLinearMap) = _
    rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _), Submodule.range_subtype]
  · intro Y hY v v' hv'
    have hX : inG ε (Y.map star) := inG_conj hY.1
    have hsm : ∀ t : ℝ, inK ε ((t : ℂ) • Y) := by
      intro t
      obtain ⟨hg, hc⟩ := hY
      unfold inG at hg
      refine ⟨?_, ?_⟩
      · unfold inG
        rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
          Matrix.mul_smul, ← smul_add, hg, smul_zero]
      · rw [Matrix.smul_mul, Matrix.mul_smul, hc]
    have hpt : ∀ t : ℝ, ((τ (NormedSpace.exp ((t : ℂ) • Y)) v : S) : H) =
        σ (NormedSpace.exp ((t : ℂ) • Y.map star)) v := by
      intro t
      rw [hτσ _ (hexpK _ (hsm t)), exp_conj]
      congr 3
      ext a b
      simp
    have hd := hD (Y.map star) hX (j v)
    rw [hjι, ← hv', hjι] at hd
    rw [hasDerivAt_iff_isLittleO] at hd ⊢
    refine Asymptotics.isLittleO_norm_left.mp ?_
    refine (Asymptotics.isLittleO_norm_left.mpr hd).congr_left fun t => ?_
    rw [Submodule.coe_norm]
    simp only [Submodule.coe_sub, Submodule.coe_smul_of_tower, hpt]

end GlobalTheory.SphJet.LowTau
end
end

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_lowestKType_complexified : ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ) (H V : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : Fin n → Fin n → Module.End ℂ V) (ι : V →ₗᵢ[ℂ] H) (u : V), IsURepOn (UJset ε) σ → DerTie ε σ E ι → ‖u‖ = 1 → IsKTypeOf ε σ Λ ((kSpan ε E u).map ι.toLinearMap) → IsWtOn (Kset ε) σ Λ (ι u) → ∃ (W : Type) (_ : NormedAddCommGroup W) (_ : InnerProductSpace ℂ W) (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W) (j : W →ₗᵢ[ℂ] V), IsTau ε Λ τ w ∧ j w = u ∧ LinearMap.range j.toLinearMap = kSpan ε E u ∧ TauTie ε E j τ := by
  atlas_forward_decl GlobalTheory.SphJet.LowTau.exists_tau
end

section
section
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

namespace GlobalTheory.SphJet

private lemma posDef_inv_toMK_mul_mul_toMK {n : ℕ} {ε : Fin n → Bool} (k : KG ε)
    {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) : ((toMK k)⁻¹ * x * toMK k).PosDef := by
  have hK : toMK k ∈ Kset ε := (mem_KG ε _).1 k.2
  have hU : star (toMK k) * toMK k = 1 := Matrix.mem_unitaryGroup_iff'.1 hK.1
  have hinv : (toMK k)⁻¹ = (toMK k)ᴴ := Matrix.inv_eq_left_inv hU
  rw [hinv]
  refine hx.conjTranspose_mul_mul_same ?_
  intro v₁ v₂ hv
  have := congrArg (fun v => (toMK k)ᴴ *ᵥ v) hv
  simpa [Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose, hU] using this

private lemma norm_inner_ps_exp_le_decHS_mul {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {W : Type}
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)}
    {w : W} (hlam : IsHCParam lam) (hτ : IsTau ε (lowK ε lam) τ w) {h : ℝ}
    (hgap : GapAtLeast ε lam h) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) (u y : W) :
    ‖⟪y, ps ε lam τ w (NormedSpace.exp X) u⟫_ℂ‖ ≤
      decHS h (rkR ε) (Real.sqrt (hs X)) * ‖u‖ * ‖y‖ := by
  have hP : (NormedSpace.exp X).PosDef := GlobalTheory.Dec.FormF.exp_posDef hX
  have hint : ∀ v : W, Integrable (fun k : KG ε => ‖⟪v, τ (toMK k) w⟫_ℂ‖ ^ 2) (muK ε) := by
    intro v
    by_contra hn
    have hs := GlobalTheory.PsiBound.schur_norm hτ v
    rw [integral_undef hn, mul_zero] at hs
    have hv : v = 0 := by
      have : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
      exact norm_eq_zero.1 this
    subst hv
    simp at hn
  have hM : 0 ≤ decHS h (rkR ε) (Real.sqrt (hs X)) := (Real.exp_pos _).le
  rw [GlobalTheory.PsiBound.ps_entry hτ lam hP u y]
  refine GlobalTheory.PsiBound.weighted_bound (muK ε) (Module.finrank ℂ W) _ _ _ _ _ _ hM (norm_nonneg u)
    (norm_nonneg y) (fun k => GlobalTheory.PsiBound.norm_Phi_le hlam hgap hX ((mem_KG ε _).1 k.2))
    (hint y) ?_ (GlobalTheory.PsiBound.schur_norm hτ y) ?_
  · simpa only [norm_inner_symm] using hint u
  · simpa only [norm_inner_symm] using GlobalTheory.PsiBound.schur_norm hτ u

theorem ps_exp_pos_bound_analytic : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), IsHCParam lam → IsTau ε (lowK ε lam) τ w → ∀ h : ℝ, GapAtLeast ε lam h → ∀ X, inP ε X → (∀ x : W, 0 ≤ ⟪x, ps ε lam τ w (NormedSpace.exp X) x⟫_ℂ) ∧ ‖ps ε lam τ w (NormedSpace.exp X)‖ ≤ decHS h (rkR ε) (Real.sqrt (hs X)) ∧ AnalyticAt ℂ (ps ε lam τ w) (NormedSpace.exp X) := by
  intro n ε lam W _ _ τ w hlam hτ h hgap X hX
  have hP : (NormedSpace.exp X).PosDef := GlobalTheory.Dec.FormF.exp_posDef hX
  refine ⟨fun x => ?_, ?_, ?_⟩
  ·
    rw [GlobalTheory.PsiBound.ps_entry hτ lam hP x x]
    set F : KG ε → ℂ := fun k => Phi lam ((toMK k)⁻¹ * NormedSpace.exp X * toMK k) *
      (⟪x, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ) with hFdef
    have hF : ∀ k, 0 ≤ F k := by
      intro k
      have hphi : 0 < Phi lam ((toMK k)⁻¹ * NormedSpace.exp X * toMK k) :=
        (phiPos n lam _ (posDef_inv_toMK_mul_mul_toMK k hP)).2.1
      have hsq : 0 ≤ ⟪x, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ := by
        rw [← inner_conj_symm x (τ (toMK k) w), mul_comm, Complex.mul_conj]
        exact Complex.zero_le_real.2 (Complex.normSq_nonneg _)
      exact mul_nonneg hphi.le hsq
    have hre : ∀ k, F k = ((F k).re : ℂ) := fun k =>
      Complex.ext rfl (by simpa using ((Complex.le_def.1 (hF k)).2).symm)
    have hI : ∫ k, F k ∂(muK ε) = ((∫ k, (F k).re ∂(muK ε) : ℝ) : ℂ) := by
      rw [integral_congr_ae (Eventually.of_forall hre)]
      first
        | exact integral_complex_ofReal
        | exact integral_ofReal
    rw [hI]
    refine mul_nonneg (Nat.cast_nonneg _) (Complex.zero_le_real.2 (integral_nonneg fun k => ?_))
    exact (Complex.le_def.1 (hF k)).1
  ·
    have hM : 0 ≤ decHS h (rkR ε) (Real.sqrt (hs X)) := (Real.exp_pos _).le
    refine ContinuousLinearMap.opNorm_le_bound _ hM fun u => ?_
    set T := ps ε lam τ w (NormedSpace.exp X)
    rcases eq_or_ne (T u) 0 with h0 | h0
    · rw [h0, norm_zero]; positivity
    have hb := norm_inner_ps_exp_le_decHS_mul hlam hτ hgap hX u (T u)
    rw [inner_self_eq_norm_sq_to_K] at hb
    simp only [norm_pow, RCLike.norm_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_norm] at hb
    have hpos : 0 < ‖T u‖ := norm_pos_iff.2 h0
    nlinarith
  ·
    obtain ⟨hopen, hpos, hdiff, -⟩ := psBasic n ε lam W τ w hlam hτ
    haveI : FiniteDimensional ℂ W := hτ.1
    haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
    let e : (Fin n → Fin n → ℂ) ≃L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
      (Matrix.ofLinearEquiv ℂ).toContinuousLinearEquiv
    have hg : AnalyticAt ℂ (fun z : Fin n → Fin n → ℂ => ps ε lam τ w (Matrix.of z))
        (e.symm (NormedSpace.exp X)) :=
      GlobalTheory.SCV.analyticAt_of_differentiableOn hdiff
        (hopen.mem_nhds (show Matrix.of _ ∈ U1 ε from hpos _ hP))
    have he : AnalyticAt ℂ (⇑e.symm) (NormedSpace.exp X) :=
      e.symm.toContinuousLinearMap.analyticAt _
    exact hg.comp he

end GlobalTheory.SphJet
end

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kAveragedMinorOperator_exp_pos_bound_analytic : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), IsHCParam lam → IsTau ε (lowK ε lam) τ w → ∀ h : ℝ, GapAtLeast ε lam h → ∀ X, inP ε X → (∀ x : W, 0 ≤ ⟪x, ps ε lam τ w (NormedSpace.exp X) x⟫_ℂ) ∧ ‖ps ε lam τ w (NormedSpace.exp X)‖ ≤ decHS h (rkR ε) (Real.sqrt (hs X)) ∧ AnalyticAt ℂ (ps ε lam τ w) (NormedSpace.exp X) := by
  atlas_forward_decl GlobalTheory.SphJet.ps_exp_pos_bound_analytic
end

section
noncomputable section

namespace GlobalTheory.SphJet

section Linear

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] {E : Fin n → Fin n → Module.End ℂ V} {u : V} {j : W →ₗᵢ[ℂ] V}
  {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {w : W}

theorem funSchmid_ps (hl : IsHCParam lam) (hτ : IsTau ε (lowK ε lam) τ w) (hD : LowData ε E (lowK ε lam) u j)
    (hw : j w = u) (ht : TauTie ε E j τ) : FunSchmid ε E (lowK ε lam) u j (ps ε lam τ w) := by
  intro G hG
  obtain ⟨hopen, hpos, -, -⟩ := GlobalTheory.Dec.psBasic n ε lam W τ w hl hτ
  have hopen' : IsOpen (U1 ε) := hopen
  filter_upwards [hopen'.mem_nhds (hpos 1 Matrix.PosDef.one)] with z hz
  refine ext_inner_left ℂ fun y => ?_
  have hd := fun p => GlobalTheory.T.inner_fderiv_kAveragedMinorOperator_integral n ε lam W τ w hl hτ z hz (z * thE ε p) y (G p)
  rw [inner_sum, inner_zero_right]
  simp only [fun p => (hd p).2]
  rw [← Finset.mul_sum, ← integral_finset_sum _ fun p _ => (hd p).1]
  refine mul_eq_zero_of_right _ (integral_eq_zero_of_ae (Eventually.of_forall fun k => ?_))
  obtain ⟨G', hG', he⟩ := GlobalTheory.T.lowerKTypes_pTensor_stable_under_K V W n ε E _ u j τ w hD hτ ht G hG (toMK k) k.2
  have hk : toMK k * (toMK k)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (TauExt.mem_KC k.2).1)
  have h0 := GlobalTheory.T.fderiv_leadingMinorPowerProduct_strictUpper_eq_zero n lam ((toMK k)⁻¹ * z * toMK k) (∑ p, ⟪w, G' p⟫_ℂ • thE ε p) (hz _ k.2) (by
    intro i i' hi
    rw [Matrix.sum_apply]
    refine Finset.sum_eq_zero fun p _ => ?_
    by_cases hp : p = (i', i)
    · subst hp
      have := GlobalTheory.T.negativeRootArray_highestVector_coeff_eq_zero V n ε E _ u hD.1 hD.2.1 hD.2.2.1 _ hG' i' i hi
      have e : ⟪w, G' (i', i)⟫_ℂ = 0 := by rw [← j.inner_map_map, hw]; exact this
      rw [e, zero_smul, Matrix.zero_apply]
    · have : Matrix.single p.2 p.1 (1 : ℂ) i i' = 0 :=
        Matrix.single_apply_of_ne _ _ _ _ _ fun h => hp (Prod.ext h.2 h.1)
      rw [thE, Matrix.smul_apply, Matrix.smul_apply, this, smul_zero, smul_zero])
  rw [← he, Matrix.mul_sum, map_sum] at h0
  have e : ∀ p, (toMK k)⁻¹ * z * toMK k * (⟪τ (toMK k) w, G p⟫_ℂ • ((toMK k)⁻¹ * thE ε p * toMK k)) =
      ⟪τ (toMK k) w, G p⟫_ℂ • ((toMK k)⁻¹ * (z * thE ε p) * toMK k) := fun p => by
    rw [Matrix.mul_smul]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (toMK k), hk, Matrix.one_mul]
  simp only [e, map_smul, smul_eq_mul] at h0
  have := congrArg (fun c => ⟪y, τ (toMK k) w⟫_ℂ * c) h0
  simp only [Finset.mul_sum, mul_zero] at this
  change ∑ p, _ = (0 : ℂ)
  rw [← this]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem apply_eq_zero_of_mem_noncompactPart {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) {a b : Fin n} (h : ε a = ε b) : X a b = 0 := by
  have := congrFun (congrFun hX.2 a) b
  simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply, h] at this
  split_ifs at this
  · linear_combination (1 / 2 : ℂ) * this
  · linear_combination (-1 / 2 : ℂ) * this

theorem thM_eq {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) : thM ε X = Xᵀ := by
  ext i i'
  rw [thM, Matrix.sum_apply, Finset.sum_eq_single (i', i)]
  · by_cases h : ε i' = ε i
    · simp [apply_eq_zero_of_mem_noncompactPart hX h]
    · simp [thE, sgn, h]
  · intro p _ hp
    have : Matrix.single p.2 p.1 (1 : ℂ) i i' = 0 :=
      Matrix.single_apply_of_ne _ _ _ _ _ fun h => hp (Prod.ext h.2 h.1)
    rw [thE, Matrix.smul_apply, Matrix.smul_apply, this, smul_zero, smul_zero]
  · simp

theorem smul_transpose_mem_noncompactPart {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) (t : ℝ) : inP ε ((t : ℂ) • Xᵀ) := by
  obtain ⟨h1, h2⟩ := (parabolic_character_holds n ε X).1.1 hX
  refine (parabolic_character_holds n ε _).1.2 ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
    congr 1
    exact congrArg Matrix.transpose h1
  · have h3 := congrArg Matrix.transpose h2
    have hJ : (Formalism.REAL.Jm ε)ᵀ = Formalism.REAL.Jm ε := Matrix.diagonal_transpose _
    rw [Matrix.transpose_neg, Matrix.transpose_mul, Matrix.transpose_mul, hJ] at h3
    rw [Matrix.smul_mul, Matrix.mul_smul, h3, smul_neg, neg_neg]

theorem compress_eq {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {ι : V →ₗᵢ[ℂ] H}
    (hl : IsHCParam lam) (hg : GapAtLeast ε lam (2 * n + 1)) (hσ : IsURepOn (UJset ε) σ) (hder : DerTie ε σ E ι)
    (hτ : IsTau ε (lowK ε lam) τ w) (hD : LowData ε E (lowK ε lam) u j) (hw : j w = u) (ht : TauTie ε E j τ)
    (hlow : ∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ x : V, KHighest ε E (lowK ε lam - root a b) x → x = 0)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) (y x : W) :
    ⟪ι (j y), σ (NormedSpace.exp X) (ι (j x))⟫_ℂ = ⟪y, ps ε lam τ w (NormedSpace.exp Xᵀ) x⟫_ℂ := by
  haveI := hτ.1
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  have han : ∀ Y, inP ε Y → AnalyticAt ℂ (ps ε lam τ w) (NormedSpace.exp Y) := fun Y hY =>
    (GlobalTheory.T.kAveragedMinorOperator_exp_pos_bound_analytic n ε lam W τ w hl hτ _ hg Y hY).2.2
  have h1 : AnalyticAt ℂ (ps ε lam τ w) 1 := by simpa using han _ (smul_transpose_mem_noncompactPart hX 0)
  have r1 := GlobalTheory.T.glWordJetRelations_of_schmidSystem_jets V W n ε E _ u j _ h1 (GlobalTheory.T.lowest_K_type_function_equivalence n ε lam W τ w hl hτ V E u j hD ht)
    (funSchmid_ps hl hτ hD hw ht)
  have r2 := GlobalTheory.T.compressedWords_glWordJetRelations_of_no_types V W n ε E _ u j hD hlow
  have r3 := GlobalTheory.T.glWordJetRelations_eq_zero_of_nil V W n ε E lam u j _ hD (fun a b hab hne => by
    have := hg a b hne
    rwa [abs_of_pos (sub_pos.2 (hl.1 hab))] at this) (r1.sub r2) (by
    ext y x
    have : ps ε lam τ w 1 = ContinuousLinearMap.id ℂ W := (GlobalTheory.Dec.psBasic n ε lam W τ w hl hτ).2.2.2
    simp [funJet_apply, modJet_apply, Rw, ew, this])
  have r4 := GlobalTheory.T.iteratedDeriv_inner_exp_eq_wordJetForms V W n ε E j _ h1 (fun l => sub_eq_zero.1 (r3 l)) X
  rw [thM_eq hX] at r4
  have hφ : ∀ y x : W, AnalyticOnNhd ℝ
      (fun t : ℝ => ⟪y, ps ε lam τ w (NormedSpace.exp ((t : ℂ) • Xᵀ)) x⟫_ℂ) Set.univ := by
    intro y x t _
    have a1 : AnalyticAt ℂ (fun s : ℂ => NormedSpace.exp (s • Xᵀ)) t :=
      (Differentiable.analyticAt fun s => (hasDerivAt_exp_smul_const (𝕂 := ℂ) Xᵀ s).differentiableAt) _
    have a2 := (((innerSL ℂ y).comp (ContinuousLinearMap.apply ℂ W x)).analyticAt _).comp
      ((han _ (smul_transpose_mem_noncompactPart hX t)).comp (f := fun s : ℂ => NormedSpace.exp (s • Xᵀ)) a1)
    exact (a2.restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt t)
  have hU : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ UJset ε := exp_indefinite_unitary_holds n ε X hX.1
  have key := GlobalTheory.T.unitaryFlow_coeff_eq_of_taylor_series H (fun t => σ (NormedSpace.exp ((t : ℂ) • X))) (fun m => ι ((actM E X ^ m) (j x)))
    (ι (j y)) _ _ (by simpa using hσ.1.1) (fun s t => by
      rw [Complex.ofReal_add, add_smul, Matrix.exp_add_of_commute _ _ ((Commute.refl X).smul_left _ |>.smul_right _)]
      exact hσ.1.2 _ (hU s) _ (hU t)) (fun t v => hσ.2.1 _ (hU t) v)
    (fun m => by rw [pow_succ', Module.End.mul_apply]; exact hder X hX.1 _) (hφ y x) (hφ x x 0 trivial)
    (fun m => by rw [r4, ι.inner_map_map]) (fun m => by rw [r4, ι.inner_map_map]; rfl) 1
  simpa using key.symm

theorem core {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {ι : V →ₗᵢ[ℂ] H} {h : ℝ}
    (hl : IsHCParam lam) (hh : GapAtLeast ε lam h) (hg : GapAtLeast ε lam (2 * n + 1))
    (hσ : IsURepOn (UJset ε) σ) (hder : DerTie ε σ E ι) (hE : GlRel E) (hUn : IsUnitary ε E) (hu : ‖u‖ = 1)
    (hhi : KHighest ε E (lowK ε lam) u) (hfin : FiniteDimensional ℂ (kSpan ε E u))
    (hK : IsKTypeOf ε σ (lowK ε lam) ((kSpan ε E u).map ι.toLinearMap))
    (hwt : IsWtOn (Kset ε) σ (lowK ε lam) (ι u))
    (hlow : ∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ x : V, KHighest ε E (lowK ε lam - root a b) x → x = 0)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) {x : H} (hx : x ∈ (kSpan ε E u).map ι.toLinearMap) :
    0 ≤ ⟪x, σ (NormedSpace.exp X) x⟫_ℂ ∧ ∀ y ∈ (kSpan ε E u).map ι.toLinearMap,
      ‖⟪y, σ (NormedSpace.exp X) x⟫_ℂ‖ ≤ decHS h (rkR ε) (Real.sqrt (hs X)) * ‖x‖ * ‖y‖ := by
  obtain ⟨W, _, _, τ, w, j, hτ, hw, hr, ht⟩ := GlobalTheory.T.exists_holomorphic_lowestKType_complexified n ε _ H V σ E ι u hσ hder hu hK hwt
  have e := compress_eq hl hg hσ hder hτ ⟨hE, hUn, hhi, hfin, hr⟩ hw ht hlow hX
  have hXt : inP ε Xᵀ := by simpa using smul_transpose_mem_noncompactPart hX 1
  obtain ⟨p1, p2, -⟩ := GlobalTheory.T.kAveragedMinorOperator_exp_pos_bound_analytic n ε lam W τ w hl hτ h hh _ hXt
  have hhs : hs Xᵀ = hs X := by unfold hs; exact Finset.sum_comm
  rw [← hr] at hx ⊢
  obtain ⟨_, ⟨x, rfl⟩, rfl⟩ := hx
  refine ⟨(e x x).symm ▸ p1 x, ?_⟩
  rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
  refine (congrArg norm (e y x)).trans_le ((norm_inner_le_norm _ _).trans ?_)
  simp only [LinearIsometry.coe_toLinearMap, LinearIsometry.norm_map]
  rw [mul_comm, ← hhs]
  exact mul_le_mul_of_nonneg_right (((ps ε lam τ w _).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right p2 (norm_nonneg _))) (norm_nonneg _)

end Linear

section Cover

open Matrix Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.MainNotions.S GlobalTheory.RealPar
open scoped InnerProductSpace ComplexOrder

variable {p q n : ℕ} {e : Ix p q ≃ Fin n} {ε : Fin n → Bool}

section Alg

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def unitOp (e : Ix p q ≃ Fin n) (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (a b : Fin n) : Module.End ℂ V :=
  act (Eab (e.symm a) (e.symm b))

theorem act_eq_sum (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (Z : Mat p q) :
    act Z = ∑ a, ∑ b, Z a b • act (Eab a b) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
  simp only [map_sum, Eab, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

theorem actM_unitOp (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (Z : Mat p q) :
    actM (unitOp e act) (Matrix.reindex e e Z) = act Z := by
  rw [act_eq_sum act Z, actM, ← e.sum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← e.sum_comp]
  simp [unitOp]

theorem glRel_unitOp {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) : Formalism.REAL.GlRel (unitOp e act) := by
  intro a b c d
  unfold unitOp
  rw [← h, map_sub]
  congr 1
  · split_ifs with h1
    · subst h1; simp [Eab]
    · rw [Eab, Eab, Matrix.single_mul_single_of_ne _ _ _ _ (e.symm.injective.ne h1), map_zero]
  · split_ifs with h1
    · subst h1; simp [Eab]
    · rw [Eab, Eab, Matrix.single_mul_single_of_ne _ _ _ _ (e.symm.injective.ne h1), map_zero]

theorem kStable_iff (h : BlockOrd e ε) (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (W : Submodule ℂ V) :
    KStable act W ↔ Formalism.REAL.KStable ε (unitOp e act) W := by
  constructor
  · intro hW a b hab x hx
    exact hW _ (isKC_Eab ((h.sameBlock_iff _ _).2 (by simpa using hab))) x hx
  · intro hW Z hZ x hx
    rw [act_eq_sum]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    refine W.sum_mem fun a _ => W.sum_mem fun b _ => ?_
    by_cases hab : sameBlock a b
    · have := hW (e a) (e b) ((h.sameBlock_iff _ _).1 hab) x hx
      simp only [unitOp, Equiv.symm_apply_apply] at this
      exact W.smul_mem _ this
    · rw [hZ a b hab, zero_smul]; exact W.zero_mem

theorem kHighest_iff (h : BlockOrd e ε) (act : Mat p q →ₗ[ℂ] Module.End ℂ V) {ν : Ix p q → ℚ} {μ : Fin n → ℝ}
    (hμ : ∀ a, (ν a : ℝ) = μ (e a)) (x : V) :
    Formalism.REAL.KHighest ε (unitOp e act) μ x ↔ x ∈ hwSub act ν := by
  rw [mem_hwSub]
  refine and_congr ?_ ?_
  · refine e.forall_congr_right.symm.trans (forall_congr' fun a => ?_)
    simp [unitOp, ← hμ]
  · refine e.forall_congr_right.symm.trans (forall_congr' fun a => ?_)
    refine e.forall_congr_right.symm.trans (forall_congr' fun b => ?_)
    simp [unitOp, h.posC_iff]

end Alg

theorem int_of_isWtOn {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (h1 : σ 1 = 1) {μ : Fin n → ℝ} {v : H} (hv0 : v ≠ 0)
    (hw : IsWtOn (Formalism.REAL.Kset ε) σ μ v) (i : Fin n) : ∃ m : ℤ, μ i = m := by
  have e1 : Matrix.diagonal (fun a => Complex.exp (((Pi.single i (2 * Real.pi) : Fin n → ℝ) a : ℂ) * Complex.I)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← Matrix.diagonal_one]
    congr 1
    funext a
    by_cases ha : a = i
    · subst ha; simp
    · simp [ha]
  have := hw (Pi.single i (2 * Real.pi)) (by rw [e1]; exact ⟨one_mem _, by simp⟩)
  rw [e1, h1] at this
  have e2 : Complex.exp (((∑ a, μ a * (Pi.single i (2 * Real.pi) : Fin n → ℝ) a : ℝ) : ℂ) * Complex.I) = 1 := by
    refine smul_left_injective ℂ hv0 ?_
    simpa using this.symm
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 e2
  refine ⟨m, ?_⟩
  simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hm
  have h3 : ((μ i : ℝ) : ℂ) = m := by
    refine mul_right_cancel₀ Complex.two_pi_I_ne_zero ?_
    rw [← hm]; push_cast; ring
  exact_mod_cast h3

theorem reindex_exp (e : Ix p q ≃ Fin n) (X : Mat p q) :
    Matrix.reindex e e (NormedSpace.exp X) = NormedSpace.exp (Matrix.reindex e e X) := by
  open scoped Matrix.Norms.Operator in
  exact NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e)
    (LinearMap.continuous_of_finiteDimensional (Matrix.reindexAlgEquiv ℂ ℂ e).toLinearMap) X

theorem inG_iff (h : BlockOrd e ε) (X : Mat p q) : Formalism.REAL.inG ε (Matrix.reindex e e X) ↔ X ∈ upq p q := by
  unfold Formalism.REAL.inG
  rw [← h.reindex_Jm, Matrix.conjTranspose_reindex]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  exact (Matrix.reindex e e).injective.eq_iff (a := Xᴴ * Jm p q + Jm p q * X) (b := 0)

theorem reindex_mem_noncompactPart (h : BlockOrd e ε) {X : Mat p q} (hX : X ∈ pR p q) : Formalism.REAL.inP ε (Matrix.reindex e e X) := by
  refine ⟨(inG_iff h X).2 hX.1, ?_⟩
  ext i j
  obtain ⟨a, rfl⟩ := e.surjective i
  obtain ⟨b, rfl⟩ := e.surjective j
  simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_apply_apply]
  by_cases hab : sameBlock a b
  · simp [hX.2 a b hab]
  · rw [h.sameBlock_iff] at hab
    cases h1 : ε (e a) <;> cases h2 : ε (e b) <;> simp_all

theorem sub_rho_int {lam : Ix p q → ℚ} (hl : Function.Injective lam) (a : Ix p q) {m : ℤ}
    (hm : blattner lam a = m) : ∃ k : ℤ, lam a - (((p + q : ℕ) : ℚ) - 1) / 2 = k := by
  classical
  have key : (Finset.univ.filter fun b => ¬ sameBlock a b ∧ lam b < lam a).card +
      (Finset.univ.filter fun b => ¬ sameBlock a b ∧ lam a < lam b).card +
      (Finset.univ.filter fun b => sameBlock a b ∧ lam b < lam a).card +
      (Finset.univ.filter fun b => sameBlock a b ∧ lam a < lam b).card + 1 = p + q := by
    have h1 : (1 : ℕ) = ∑ b, if b = a then 1 else 0 := by simp
    have h2 : p + q = ∑ _b : Ix p q, 1 := by simp
    rw [h2]
    simp only [Finset.card_filter]
    nth_rewrite 5 [h1]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : b = a
    · subst hb; simp
    · rcases lt_or_gt_of_ne (hl.ne hb) with h | h <;> by_cases hs : sameBlock a b <;> simp [hb, hs, h, h.not_gt]
  refine ⟨m - (Finset.univ.filter fun b => ¬ sameBlock a b ∧ lam b < lam a).card -
    (Finset.univ.filter fun b => sameBlock a b ∧ lam a < lam b).card, ?_⟩
  unfold blattner rhoNC at hm
  rw [← key]
  push_cast
  linarith

variable {T : GrpData p q}

theorem exists_blockOrd_std (p q : ℕ) :
    BlockOrd (finSumFinEquiv : Ix p q ≃ Fin (p + q)) fun i => (finSumFinEquiv.symm i).isLeft := by
  refine ⟨fun i => by simp, fun i => by simp, ?_⟩
  rintro (a | a) (b | b) hab
  · exact hab
  · exact hab.elim
  · exact hab.elim
  · exact Nat.add_lt_add_left hab p

theorem exists_isHW {V : Type} [AddCommGroup V] [Module ℂ V] {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {μ : Ix p q → ℚ}
    (h : Module.finrank ℂ (hwSub act μ) = 1) : ∃ v, IsHW act μ v ∧ ∀ x ∈ hwSub act μ, ∃ c : ℂ, c • v = x := by
  obtain ⟨v, hv, hs⟩ := finrank_eq_one_iff'.1 h
  exact ⟨v, ⟨fun h0 => hv (Subtype.ext h0), v.2⟩, fun x hx => (hs ⟨x, hx⟩).imp fun c hc => congrArg Subtype.val hc⟩

theorem not_below {lam : Ix p q → ℚ} {a b : Ix p q} (hab : lam b < lam a) {m : Ix p q → Ix p q → ℕ}
    (hm : ∀ a b, m a b ≠ 0 → lam b < lam a) :
    ¬ ∀ c, -((if c = a then 1 else 0) - (if c = b then 1 else 0) : ℚ) =
      ∑ a, ∑ b, (m a b : ℚ) * ((if c = a then 1 else 0) - (if c = b then 1 else 0)) := by
  intro h
  have r : ∀ a b : Ix p q, ∑ c, lam c * ((if c = a then 1 else 0) - (if c = b then 1 else 0) : ℚ) = lam a - lam b := by
    intro a b
    simp [mul_sub, Finset.sum_sub_distrib]
  have h1 : -(lam a - lam b) = ∑ a, ∑ b, (m a b : ℚ) * (lam a - lam b) := by
    simp only [← r, ← Finset.sum_neg_distrib, ← mul_neg, h, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring
  have h2 : 0 ≤ ∑ a, ∑ b, (m a b : ℚ) * (lam a - lam b) :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by
      by_cases h0 : m a b = 0
      · simp [h0]
      · exact mul_nonneg (Nat.cast_nonneg _) (sub_pos.2 (hm a b h0)).le
  linarith

theorem of_trivial (R : DSRep T) (hker : ∀ x, T.cov x = 1 → R.U.π x = 1) {lam : Ix p q → ℚ} (hl : IsParam lam)
    (h1 : Module.finrank ℂ (hwSub R.HK.act (blattner lam)) = 1)
    (hc : ∀ (μ : Ix p q → ℚ) v, IsHW R.HK.act μ v →
      ∃ m : Ix p q → Ix p q → ℕ, (∀ a b, m a b ≠ 0 → lam b < lam a) ∧
        ∀ c, μ c = blattner lam c +
          ∑ a, ∑ b, (m a b : ℚ) * ((if c = a then 1 else 0) - (if c = b then 1 else 0)))
    {h : ℝ} (hh : GapGe lam h) (hg : GapGe lam (2 * (p + q : ℕ) + 1)) {Y : Mat p q} (hY : Y ∈ pR p q)
    {x : R.U.H} (hx : x ∈ isoVec R (blattner lam)) :
    0 ≤ ⟪x, R.U.π (T.expt Y) x⟫_ℂ ∧ ∀ k ∈ T.Kset, ∀ y ∈ isoVec R (blattner lam),
      ‖⟪y, R.U.π (k * T.expt Y) x⟫_ℂ‖ ≤
        Real.exp (-(h / 8) * min (hsNorm Y ^ 2) (hsNorm Y / Real.sqrt (2 * (min p q : ℕ)))) * ‖x‖ * ‖y‖ := by
  classical
  obtain ⟨u₀, hu₀, hs₀⟩ := exists_isHW h1
  have inj : ∀ {v : R.HK.V}, v ≠ 0 → R.ι v ≠ 0 := fun h h0 => h (R.ι_inj (by rw [h0, map_zero]))
  have wint : ∀ {n : ℕ} {e : Ix p q ≃ Fin n} {ε : Fin n → Bool}, BlockOrd e ε → ∀ (μ : Fin n → ℝ) (v : R.HK.V),
      v ≠ 0 → (∀ a, R.HK.act (Eab a a) v = ((μ (e a) : ℝ) : ℂ) • v) → ∀ i, ∃ m : ℤ, μ i = m := by
    intro n e ε hb μ v hv hw
    obtain ⟨σ, hσ⟩ := exists_factors R.U e hker
    exact int_of_isWtOn (CoverURep.urep_irred p q n e ε T R σ hb hσ).1.1.1 (inj hv)
      ((TorusWt.isWtOn_iff p q n e ε T R σ hb hσ μ v).2 hw)
  have hi : ∀ a, ∃ m : ℤ, lam a - (((p + q : ℕ) : ℚ) - 1) / 2 = m := fun a => by
    obtain ⟨m, hm⟩ := wint (exists_blockOrd_std p q) (fun i => (blattner lam (finSumFinEquiv.symm i) : ℝ)) u₀ hu₀.1
      (fun a => by simpa using ((mem_hwSub _ _ _).1 hu₀.2).1 a) (finSumFinEquiv a)
    rw [Equiv.symm_apply_apply] at hm
    exact sub_rho_int hl.1 a (m := m) (by exact_mod_cast hm)
  obtain ⟨P, e, hsig, hb, hP⟩ := exists_blockPar hl hi
  have hle : ∀ a, (lam a : ℝ) = P.lam (e a) := fun a => by rw [hP]; exact ratEntry_cast P (e a)
  have hΛ : ∀ a, (blattner lam a : ℝ) = Formalism.QuantumDeterminants.lowK P.sgn P.lam (e a) := blattner_eq P hb hle
  obtain ⟨σ, hσ⟩ := exists_factors R.U e hker
  have hU := (CoverURep.urep_irred p q _ e _ T R σ hb hσ).1
  have gap : ∀ h : ℝ, GapGe lam h → Formalism.QuantumDeterminants.GapAtLeast P.sgn P.lam h := fun h hh i j hij => by
    obtain ⟨a, rfl⟩ := e.surjective i
    obtain ⟨b, rfl⟩ := e.surjective j
    have := hh a b (by rwa [hb.sameBlock_iff])
    rwa [Rat.cast_sub, hle, hle] at this
  have hexp : ∀ X ∈ upq p q, R.U.π (T.expt X) = σ (NormedSpace.exp (Matrix.reindex e e X)) := fun X hX => by
    rw [hσ, T.expt_cov X hX, reindex_exp]
  letI : NormedAddCommGroup R.HK.V := NormedAddCommGroup.induced _ _ R.ι R.ι_inj
  letI : InnerProductSpace ℂ R.HK.V := InnerProductSpace.induced R.ι
  let ι : R.HK.V →ₗᵢ[ℂ] R.U.H := ⟨R.ι, fun _ => rfl⟩
  set E := unitOp e R.HK.act with hE
  have hder : DerTie P.sgn σ E ι := by
    intro X hX v
    obtain ⟨X, rfl⟩ := (Matrix.reindex e e).surjective X
    have hX' := (inG_iff hb X).1 hX
    rw [hE, actM_unitOp]
    have := R.der X hX' v
    simp only [hexp _ (KStabLie.smul_mem_upq hX' _)] at this
    exact this
  have hG : Formalism.REAL.GlRel E := glRel_unitOp R.HK.lie
  have hUn : Formalism.REAL.IsUnitary P.sgn E := by
    intro i j x y
    obtain ⟨a, rfl⟩ := e.surjective i
    obtain ⟨b, rfl⟩ := e.surjective j
    have h2 := DerivedAdjoint.derived_adjoint p q T R.U R.HK R.ι R.der (Eab a b) x y
    have h3 : adjZ (Eab a b) = ((Formalism.REAL.sgn P.sgn (e a) (e b) : ℝ) : ℂ) • Eab b a := by
      rw [adjZ, KStabLie.Jm_eq, Eab, Matrix.conjTranspose_single]
      ext c d
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      by_cases hcd : b = c ∧ a = d
      · obtain ⟨rfl, rfl⟩ := hcd
        cases a <;> cases b <;> simp [Formalism.REAL.sgn, hb.1, hb.2.1, Eab]
      · simp [Eab, Matrix.single_apply, hcd]
    rw [h3, map_smul, LinearMap.smul_apply, map_smul, inner_smul_right] at h2
    simp only [hE, unitOp, Equiv.symm_apply_apply]
    exact h2
  set u : R.HK.V := ((‖u₀‖⁻¹ : ℝ) : ℂ) • u₀ with hu
  have hn0 : ‖u₀‖ ≠ 0 := norm_ne_zero_iff.2 hu₀.1
  have hu1 : ‖u‖ = 1 := by rw [hu, norm_smul]; simp [hn0]
  have huw : IsHW R.HK.act (blattner lam) u :=
    ⟨fun h0 => by simp [h0] at hu1, Submodule.smul_mem _ _ hu₀.2⟩
  have hhi := (kHighest_iff hb R.HK.act hΛ u).2 huw.2
  have hks := (kStable_iff hb R.HK.act _).2 (Formalism.REAL.compact_span_compact_stable P.sgn E u)
  have hmin : ∀ W : Submodule ℂ R.HK.V, u ∈ W → KStable R.HK.act W → Formalism.REAL.kSpan P.sgn E u ≤ W :=
    fun W a b => sInf_le ⟨a, (kStable_iff hb _ _).1 b⟩
  have hfin : FiniteDimensional ℂ (Formalism.REAL.kSpan P.sgn E u) := by
    obtain ⟨W, a, b, c⟩ := R.HK.kfin u
    exact Submodule.finiteDimensional_of_le (hmin W b c)
  have kr := Formalism.REAL.glRel_kRel P.sgn E hG
  have ku := Formalism.REAL.isUnitary_kUnit P.sgn E hUn
  have hwt : IsWtOn (Formalism.REAL.Kset P.sgn) σ (Formalism.QuantumDeterminants.lowK P.sgn P.lam) (R.ι u) :=
    (TorusWt.isWtOn_iff p q _ e _ T R σ hb hσ _ u).2 fun a => by
      simpa [← hΛ] using ((mem_hwSub _ _ _).1 huw.2).1 a
  have hK : IsKTypeOf P.sgn σ (Formalism.QuantumDeterminants.lowK P.sgn P.lam) ((Formalism.REAL.kSpan P.sgn E u).map R.ι) := by
    refine ⟨inferInstance, isKStableOn_of_kStable p q _ e _ T R σ hb hσ _ hfin hks, fun S' a b => ?_,
      ⟨R.ι u, ⟨u, Formalism.REAL.mem_kSpan_self' _ _ _, rfl⟩, inj huw.1, hwt⟩, ?_⟩
    · obtain ⟨-, a1, a2⟩ := comap_kstable R hb hσ (Submodule.finiteDimensional_of_le a) b
      rcases Formalism.REAL.kIrr _ _ P.sgn E _ u hfin kr ku hhi (S'.comap R.ι)
        ((Submodule.comap_mono a).trans (Submodule.comap_map_eq_of_injective R.ι_inj _).le)
        ((kStable_iff hb _ _).1 a2) with h0 | h0
      · left; rw [← a1, h0, Submodule.map_bot]
      · right; rw [← a1, h0]
    · obtain ⟨W0, c1, c2, -, c4⟩ := HwGen.hw_generated p q R.HK.V R.HK.act R.HK.lie _ u huw
      rintro ν _ ⟨w, hw, rfl⟩ hw0 hwt
      obtain ⟨c, d1, d2⟩ := c4 (fun a => ν (e a)) w (hmin W0 c1 c2 hw) (fun h0 => hw0 (by rw [h0, map_zero]))
        ((TorusWt.isWtOn_iff p q _ e _ T R σ hb hσ _ w).1 hwt)
      refine ⟨fun i j => c (e.symm i) (e.symm j), fun i j hij => by simpa using (hb.posC_iff _ _).1 (d1 _ _ hij), ?_⟩
      funext i
      obtain ⟨x, rfl⟩ := e.surjective i
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← hΛ, d2]
      rw [← e.sum_comp]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← e.sum_comp]
      simp only [Equiv.symm_apply_apply, root_apply]
  have hlow : ∀ i j, i < j → P.sgn i ≠ P.sgn j → ∀ x, Formalism.REAL.KHighest P.sgn E
      (Formalism.QuantumDeterminants.lowK P.sgn P.lam - Formalism.REAL.root i j) x → x = 0 := by
    intro i j hij _ x hx
    obtain ⟨a, rfl⟩ := e.surjective i
    obtain ⟨b, rfl⟩ := e.surjective j
    by_contra h0
    obtain ⟨m, m1, m2⟩ := hc (fun c => blattner lam c - ((if c = a then 1 else 0) - (if c = b then 1 else 0))) x
      ⟨h0, (kHighest_iff hb _ (fun c => by
        rw [Pi.sub_apply, root_apply, ← hΛ]; split_ifs <;> simp) x).1 hx⟩
    refine not_below (a := a) (b := b) ?_ m1 fun c => by linarith [m2 c]
    have := P.hc.1 hij
    rw [← hle, ← hle] at this
    exact_mod_cast this
  have hiso : ∀ x ∈ isoVec R (blattner lam), x ∈ (Formalism.REAL.kSpan P.sgn E u).map R.ι := by
    rintro _ ⟨v, ⟨W, a, b, c, d⟩, rfl⟩
    refine ⟨v, ?_, rfl⟩
    obtain ⟨m, x, μ, f1, -, f2⟩ := Formalism.REAL.kDecomp _ _ P.sgn E W a kr ku ((kStable_iff hb _ _).1 c)
    rw [← f2] at b
    refine (iSup_le fun i => ?_ : _ ≤ Formalism.REAL.kSpan P.sgn E u) b
    obtain ⟨g1, g2, g3⟩ := f1 i
    choose z hz using wint hb (μ i) (x i) g2 fun a => by simpa [hE, unitOp] using g3.1 (e a)
    have g4 := (kHighest_iff hb R.HK.act (ν := fun a => (z (e a) : ℚ)) (fun a => by simp [hz]) _).1 g3
    rw [d _ _ g1 ⟨g2, g4⟩] at g4
    obtain ⟨c, hc⟩ := hs₀ _ g4
    refine sInf_le ⟨?_, Formalism.REAL.compact_span_compact_stable P.sgn E u⟩
    have : x i = (c * (‖u₀‖ : ℝ)) • u := by
      rw [hu, smul_smul, mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hn0, ← hc]; simp
    rw [this]
    exact Submodule.smul_mem _ _ (Formalism.REAL.mem_kSpan_self' _ _ _)
  obtain ⟨r1, r2⟩ := core (ι := ι) P.hc (gap h hh) (gap _ hg) hU hder hG hUn hu1 hhi hfin hK hwt hlow
    (reindex_mem_noncompactPart hb hY) (hiso x hx)
  rw [← hexp Y hY.1] at r1 r2
  refine ⟨r1, fun k hk y hy => ?_⟩
  have hk' := Formalism.REAL.Kset_star _ (KStabLie.mem_Kset hb T hk)
  have hk2 : R.U.π k⁻¹ y ∈ (Formalism.REAL.kSpan P.sgn E u).map R.ι := by
    have hki : k⁻¹ ∈ T.Kset := by
      have h3 : Commute ((T.cov k : GL (Ix p q) ℂ) : Mat p q) (Jm p q) := (KStabLie.isKC_iff _).1 hk
      change IsKC _
      rw [KStabLie.isKC_iff, map_inv]
      exact h3.units_inv_left
    rw [hσ]
    exact hK.2.1 _ (KStabLie.mem_Kset hb T hki) y (hiso y hy)
  have r3 := r2 _ hk2
  rw [R.U.isom, ← DerivedAdjoint.inner_map T R.U k, ← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel,
    map_one, ← ContinuousLinearMap.mul_apply, ← map_mul, ContinuousLinearMap.one_apply] at r3
  have e1 : GlobalTheory.Count.rkR P.sgn = min p q := congrArg₂ min hsig.1 hsig.2
  have e2 : Real.sqrt (Formalism.REAL.hs (Matrix.reindex e e Y)) = hsNorm Y := by
    unfold Formalism.REAL.hs hsNorm
    congr 1
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← e.sum_comp]
    simp
  rwa [e1, e2] at r3

theorem sq_expt {Y : Mat p q} (hY : Y ∈ pR p q) : ((T.sq (T.expt Y) : ℂˣ) : ℂ) = 1 := by
  have h1 := T.expt_add Y hY.1 (1 / 2) (1 / 2)
  rw [add_halves, one_smul] at h1
  have h2 : ((1 / 2 : ℝ) • Y).trace = 0 :=
    Finset.sum_eq_zero fun a _ => by
      have : Y a a = 0 := hY.2 a a (by cases a <;> trivial)
      simp [this]
  rw [h1, map_mul, Units.val_mul, ← sq, T.sq_sq, T.expt_cov _ (KStabLie.smul_mem_upq hY.1 _), GlobalTheory.DetSqrtCover.det_exp, h2,
    Complex.exp_zero]

theorem hwSub_twAct {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) :
    hwSub (Cover.twAct act) μ = hwSub act fun a => μ a + 1 / 2 := by
  ext v
  by_cases hv : v = 0
  · simp [hv]
  · simpa [IsHW, hv] using Cover.isHW_twAct act μ v

theorem isoVec_twist (R : DSRep T) {μ : Ix p q → ℚ} {x : R.U.H} (hx : x ∈ isoVec R fun a => μ a + 1 / 2) :
    x ∈ isoVec (Cover.twist R) μ := by
  obtain ⟨v, ⟨W, a, b, c, d⟩, rfl⟩ := hx
  refine ⟨v, ⟨W, a, b, fun X hX w hw => ?_, fun ν w hw h => ?_⟩, rfl⟩
  · exact (Cover.twAct_apply R.HK.act X w).symm ▸ W.sub_mem (c X hX w hw) (W.smul_mem (X.trace / 2) hw)
  · have := d _ w hw ((Cover.isHW_twAct R.HK.act ν w).1 h)
    funext a
    exact add_right_cancel (congrFun this a)

theorem of_any (R : DSRep T) {lam : Ix p q → ℚ} (hl : IsParam lam)
    (h1 : Module.finrank ℂ (hwSub R.HK.act (blattner lam)) = 1)
    (hc : ∀ (μ : Ix p q → ℚ) v, IsHW R.HK.act μ v →
      ∃ m : Ix p q → Ix p q → ℕ, (∀ a b, m a b ≠ 0 → lam b < lam a) ∧
        ∀ c, μ c = blattner lam c +
          ∑ a, ∑ b, (m a b : ℚ) * ((if c = a then 1 else 0) - (if c = b then 1 else 0)))
    {h : ℝ} (hh : GapGe lam h) (hg : GapGe lam (2 * (p + q : ℕ) + 1)) {Y : Mat p q} (hY : Y ∈ pR p q)
    {x : R.U.H} (hx : x ∈ isoVec R (blattner lam)) :
    0 ≤ ⟪x, R.U.π (T.expt Y) x⟫_ℂ ∧ ∀ k ∈ T.Kset, ∀ y ∈ isoVec R (blattner lam),
      ‖⟪y, R.U.π (k * T.expt Y) x⟫_ℂ‖ ≤
        Real.exp (-(h / 8) * min (hsNorm Y ^ 2) (hsNorm Y / Real.sqrt (2 * (min p q : ℕ)))) * ‖x‖ * ‖y‖ := by
  rcases Cover.trivial_or_twist R with hker | hker
  · exact of_trivial R hker hl h1 hc hh hg hY hx
  set lam' : Ix p q → ℚ := fun a => lam a + -(1 / 2) with hlam
  have hb : (fun a => blattner lam' a + 1 / 2) = blattner lam := by
    rw [hlam, Cover.blattner_add]
    funext a
    ring
  have hgap : ∀ h, GapGe lam h → GapGe lam' h := fun h hh a b hab => by simpa [hlam] using hh a b hab
  have hl' : IsParam lam' := by
    refine ⟨fun a b hab => hl.1 (add_right_cancel hab), fun a b hab => by simpa [hlam] using hl.2.1 a b hab,
      fun a => ?_, fun a b => by simpa [hlam] using hl.2.2.2 a b⟩
    obtain ⟨k, hk⟩ := hl.2.2.1 a
    exact ⟨k - 1, by simp only [hlam]; push_cast; linarith⟩
  obtain ⟨r1, r2⟩ := of_trivial (Cover.twist R) hker hl'
    (by rw [← hb, ← hwSub_twAct] at h1; exact h1)
    (fun μ v hv => by
      obtain ⟨m, m1, m2⟩ := hc _ v ((Cover.isHW_twAct R.HK.act μ v).1 hv)
      refine ⟨m, fun a b hab => by simpa [hlam] using m1 a b hab, fun c => ?_⟩
      have := congrFun hb c
      linarith [m2 c])
    (hgap _ hh) (hgap _ hg) hY (isoVec_twist R (hb.symm ▸ hx))
  refine ⟨?_, fun k hk y hy => ?_⟩
  · change 0 ≤ ⟪x, ((T.sq (T.expt Y) : ℂˣ) : ℂ)⁻¹ • R.U.π (T.expt Y) x⟫_ℂ at r1
    rwa [sq_expt hY, inv_one, one_smul] at r1
  · have r3 := r2 k hk y (isoVec_twist R (hb.symm ▸ hy))
    change ‖⟪y, ((T.sq (k * T.expt Y) : ℂˣ) : ℂ)⁻¹ • R.U.π (k * T.expt Y) x⟫_ℂ‖ ≤ _ at r3
    rwa [inner_smul_right, norm_mul, norm_inv, Cover.norm_sq, inv_one, one_mul] at r3

theorem lowest_type_positive_and_decays : ∀ X : ProvA, DiscreteSeriesBlattner X → admQ5 X → admQ7 → admQ8 → DiscreteSeriesPositivity X := by
  intro X h1 _ _ _ p q lam hl h hh hr
  obtain ⟨a, -, c⟩ := h1 p q lam hl
  have hg : GapGe lam (2 * (p + q : ℕ) + 1) := by
    intro i j hij
    refine le_trans (le_trans ?_ hr) (hh i j hij)
    have hpq : 1 ≤ p ∧ 1 ≤ q := by
      rcases i with i | i <;> rcases j with j | j
      · exact (hij trivial).elim
      · exact ⟨i.pos, j.pos⟩
      · exact ⟨j.pos, i.pos⟩
      · exact (hij trivial).elim
    have h2 : (1 : ℝ) ≤ ((min p q : ℕ) : ℝ) ^ ((3 : ℝ) / 2) :=
      Real.one_le_rpow (by exact_mod_cast le_min hpq.1 hpq.2) (by norm_num)
    have h3 : (1 : ℝ) ≤ ((p + q : ℕ) : ℝ) := by exact_mod_cast hpq.1.trans (Nat.le_add_right p q)
    unfold rangeOfSeventhSum
    nlinarith
  have key := fun (Y : Mat p q) (hY : Y ∈ pR p q) x hx => of_any (X.ds p q lam) hl a
    (fun μ v hv => (c μ v hv).imp fun m hm => ⟨hm.1, congrFun hm.2⟩) hh hg hY (x := x) hx
  refine ⟨fun Y hY x hx => ?_, fun k hk Y hY x hx y hy => (key Y hY x hx).2 k hk y hy⟩
  have := Complex.nonneg_iff.1 (key Y hY x hx).1
  exact ⟨this.2.symm, this.1⟩

end Cover

end GlobalTheory.SphJet
end
end
