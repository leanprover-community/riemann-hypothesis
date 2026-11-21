import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicLinearIndependent
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnfoldingConstantTermsAgreeAtGoodEmbeddings
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.GamAtOfLawsJ
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.BddSecCuspCongr
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspFDOfCuspFiniteClaim
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicFormFrameExpansion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramSchmidtFlagDomainOrthonormalFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameUnitCorrespondence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanCharacterDetPower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterTrivialOnSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastWeightPositive
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitDetRoot
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameHeckeCharTrivialOnFiniteUnitsCongOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightLabelAtUnfolding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorAnnihilatedStatement
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodEmbeddingLabelIff

section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

open scoped Matrix.Norms.Operator in

theorem commute_of_countable_commutators_exp {n : ℕ} (X a : Matrix (Fin n) (Fin n) ℂ)
    (S : Set (Matrix (Fin n) (Fin n) ℂ)) (ha : IsUnit a.det) (hS : S.Countable)
    (h : ∀ t : ℝ, NormedSpace.exp (t • X) * a * NormedSpace.exp (-(t • X)) * a⁻¹ ∈ S) :
    X * a = a * X := by
  have hd : ∀ t : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp (u • X))
      (NormedSpace.exp (t • X) * X) t := fun t => hasDerivAt_exp_smul_const X t
  have hc : Continuous (fun u : ℝ => NormedSpace.exp (u • X)) :=
    continuous_iff_continuousAt.2 fun t => (hd t).continuousAt
  have hc' : Continuous (fun u : ℝ => NormedSpace.exp (-(u • X))) := by
    have := hc.comp continuous_neg
    refine this.congr fun u => ?_
    simp [Function.comp, neg_smul]
  set f : ℝ → Matrix (Fin n) (Fin n) ℂ :=
    fun t => NormedSpace.exp (t • X) * a * NormedSpace.exp (-(t • X)) * a⁻¹ with hf
  have hfc : Continuous f := ((hc.mul continuous_const).mul hc').mul continuous_const
  have hcount : (Set.range f).Countable := hS.mono (by rintro _ ⟨t, rfl⟩; exact h t)
  have hsub : (Set.range f).Subsingleton :=
    hcount.isTotallyDisconnected _ subset_rfl (isPreconnected_range hfc)
  have hone : ∀ t, f t = 1 := by
    intro t
    rw [hsub ⟨t, rfl⟩ ⟨0, rfl⟩]
    simp [hf, Matrix.mul_nonsing_inv a ha]
  have hcomm : ∀ t : ℝ, NormedSpace.exp (t • X) * a = a * NormedSpace.exp (t • X) := by
    intro t
    have h1 := hone t
    have h2 : NormedSpace.exp (-(t • X)) * NormedSpace.exp (t • X) = 1 := by
      rw [← Matrix.exp_add_of_commute _ _ (Commute.refl (t • X)).neg_left]
      simp
    have h3 : f t * a * NormedSpace.exp (t • X) = NormedSpace.exp (t • X) * a := by
      simp only [hf]
      rw [Matrix.mul_assoc _ a⁻¹ a, Matrix.nonsing_inv_mul a ha, Matrix.mul_one,
        Matrix.mul_assoc _ (NormedSpace.exp (-(t • X))), h2, Matrix.mul_one]
    rw [← h3, h1, Matrix.one_mul]
  have e1 := (hd 0).mul_const a
  have e2 := (hd 0).const_mul a
  simp only [hcomm] at e1
  have := e1.unique e2
  simpa using this

theorem central_of_countable_commutators_unitary :
    ∀ (n : ℕ) (J a : Matrix (Fin n) (Fin n) ℂ) (S : Set (Matrix (Fin n) (Fin n) ℂ)), Jᴴ = J → IsUnit J.det → IsUnit a.det → S.Countable → (∀ X ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0}, ∀ t : ℝ, NormedSpace.exp (t • X) * a * NormedSpace.exp (-(t • X)) * a⁻¹ ∈ S) → ∀ u, u * a = a * u := by
  intro n J a S hJ hJu ha hS h u
  have key : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * J + J * X = 0 → X * a = a * X :=
    fun X hX => commute_of_countable_commutators_exp X a S ha hS (h X hX)
  set v : Matrix (Fin n) (Fin n) ℂ := J⁻¹ * uᴴ * J with hv
  have hJv : J * v = uᴴ * J := by
    rw [hv, Matrix.mul_assoc, ← Matrix.mul_assoc J, Matrix.mul_nonsing_inv J hJu, Matrix.one_mul]
  have hvJ : vᴴ * J = J * u := by
    have := congrArg Matrix.conjTranspose hJv
    simpa [Matrix.conjTranspose_mul, hJ] using this
  have h1 := key (u - v) (by
    rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, hJv, hvJ]; abel)
  have h2 := key (Complex.I • (u + v)) (by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.add_mul, Matrix.mul_add, hJv, hvJ, add_comm (J * u), ← add_smul]
    simp)
  rw [Matrix.smul_mul, Matrix.mul_smul] at h2
  have h3 : (u + v) * a = a * (u + v) := smul_right_injective _ Complex.I_ne_zero h2
  have h4 : (2 : ℂ) • (u * a) = (2 : ℂ) • (a * u) := by
    rw [Matrix.sub_mul, Matrix.mul_sub] at h1
    rw [Matrix.add_mul, Matrix.mul_add] at h3
    rw [two_smul, two_smul]
    calc u * a + u * a = (u * a - v * a) + (u * a + v * a) := by abel
      _ = (a * u - a * v) + (a * u + a * v) := by rw [h1, h3]
      _ = a * u + a * u := by abel
  exact smul_right_injective _ two_ne_zero h4

end GlobalTheory
end

section
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead

variable {D : D7}

theorem archM_mul' (V : HSp D) (th : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (g g' : GA D V) :
    archM V th (g * g') = archM V th g * archM V th g' := by
  simp only [archM, map_mul, Units.val_mul, Matrix.map_mul]

theorem archM_one' (V : HSp D) (th : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) :
    archM V th 1 = 1 := by
  simp only [archM, map_one, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem archM_det_unit (V : HSp D) (th : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (g : GA D V) :
    IsUnit (archM V th g).det :=
  Matrix.isUnit_det_of_right_inverse (B := archM V th g⁻¹) (by rw [← archM_mul', mul_inv_cancel, archM_one'])

theorem archM_rational (V : HSp D) (δ : GA D V) (hδ : δ ∈ GQ V) :
    ∃ δ₀ : GL (Fin V.rank) D.host.E,
      ∀ (τ : D.host.E →+* ℂ) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), IsInfEmb τ θ →
        archM V θ δ = δ₀.1.map τ := by
  obtain ⟨δ₀, -, he⟩ := hδ
  have he' : ∀ i j, (matHom V δ).1 i j = (1 : AF D.host.F) ⊗ₜ δ₀.1 i j := fun i j =>
    (congrArg (fun x : GL (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E) => x.1 i j) he).symm
  refine ⟨δ₀, fun τ θ hθ => ?_⟩
  ext i j
  change θ (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom V δ).1 i j)) = _
  rw [he', Algebra.TensorProduct.map_tmul, map_one]
  exact hθ.1 _

theorem exp_unitary_of_lie {n : ℕ} {J X : Matrix (Fin n) (Fin n) ℂ} (hJ : IsUnit J.det) (hX : Xᴴ * J + J * X = 0) :
    NormedSpace.exp X ∈ Formalism.QuantumDeterminants.UH J := by
  have h1 : Xᴴ = J * (-X) * J⁻¹ := by
    rw [mul_neg, ← eq_neg_of_add_eq_zero_left hX, mul_nonsing_inv_cancel_right _ _ hJ]
  change (NormedSpace.exp X)ᴴ * J * NormedSpace.exp X = J
  rw [← Matrix.exp_conjTranspose, h1, Matrix.exp_conj _ _ ((isUnit_iff_isUnit_det J).2 hJ),
    nonsing_inv_mul_cancel_right _ _ hJ, Matrix.mul_assoc,
    ← Matrix.exp_add_of_commute _ _ (Commute.refl X).neg_left, neg_add_cancel, NormedSpace.exp_zero, Matrix.mul_one]

theorem negFirst_of_orth (V : HSp D) (X : Data D.host.E V.rank) (hW : ModelW V rfl X)
    (hΨ : ∀ ρ, tauE D ρ ∈ X.Ψ) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hO : IsOrthogonalFrame X x₀) :
    NegFirst V X.p0 fun ρ => x₀ (tauE D ρ) := by
  intro ρ
  have h := hO _ (hΨ ρ)
  have hG : X.Gm = -V.gram.transpose := by
    rw [hW.1]; rfl
  ext b a
  have h1 := congrFun (congrFun h a) b
  have h2 : ((x₀ (tauE D ρ))ᴴ * gramAt D V ρ * x₀ (tauE D ρ)) b a =
      -ReciprocityTheory.ChartRestriction.G.FD.gram (tauE D ρ) X.Gm (x₀ (tauE D ρ)) a b := by
    simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, hG, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      gramAt, Matrix.map_apply, Matrix.neg_apply, Matrix.transpose_apply, map_neg, Finset.sum_mul,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [starRingEnd_apply]
    ring
  show ((x₀ (tauE D ρ))ᴴ * gramAt D V ρ * x₀ (tauE D ρ)) b a = _
  rw [h2, h1]
  by_cases hab : a = b
  · subst hab
    simp only [Matrix.diagonal_apply_eq, sgn]
    split_ifs <;> simp
  · rw [Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ (Ne.symm hab), neg_zero]

theorem NegFirst.det_unit {V : HSp D} {q : ℕ} {x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (h : NegFirst V q x) (ρ : D.what₂.Tau) : IsUnit (x ρ).det := by
  have h1 := congrArg Matrix.det (h ρ)
  rw [Matrix.det_mul, Matrix.det_diagonal] at h1
  rw [isUnit_iff_ne_zero]
  intro h0
  rw [h0, mul_zero] at h1
  refine (Finset.prod_ne_zero_iff.2 fun c _ => ?_) h1.symm
  split_ifs <;> simp

theorem baseDict_of_frames (V : HSp D) {r : ℕ} (hr : V.rank = r) {Comp : Type} (X : Comp → Data D.host.E r)
    (dict : GA D V → Σ k, Frame (X k).Ψ r) (Kf : Subgroup (GA D V))
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ)
    (th th' : ∀ k, (X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (hth : ∀ k τ, IsInfEmb τ.1 (th k τ)) (hth' : ∀ k τ, IsInfEmb τ.1 (th' k τ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (hΨ : ∀ k τ, τ ∈ (X k).Ψ ↔ ∃ ρ, τ = tauE D ρ) (hW : ∀ k, ModelW V hr (X k)) (hO : ∀ k, IsOrthogonalFrame (X k) x₀)
    (hD : DictIsUnif V dict Kf th hr)
    (hL : ∀ h, ∃ γ ∈ GQ V, ∀ τ : (X (dict h).1).Ψ, mat (dict h).2 τ =
      Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th' (dict h).1 τ) (γ * h)) * x₀ τ.1) :
    ∃ x, BaseDict θ V hr X dict Kf x := by
  subst hr
  have hre : ∀ M : Matrix (Fin V.rank) (Fin V.rank) ℂ,
      Matrix.reindex (finCongr (rfl : V.rank = V.rank)) (finCongr rfl) M = M := fun M => rfl
  obtain ⟨-, -, ⟨x0, hx0, hmul⟩, -, -, hfib⟩ := hD
  have e1 : ∀ k (τ : (X k).Ψ) ρ, τ.1 = tauE D ρ → th k τ = θ ρ := fun k τ ρ e =>
    GlobalTheory.SmoothForms.RealPts.infEmb_unique τ.1 _ _ (hth k τ) (e ▸ hθ ρ)
  have e2 : ∀ k (τ : (X k).Ψ) ρ, τ.1 = tauE D ρ → th' k τ = θ ρ := fun k τ ρ e =>
    GlobalTheory.SmoothForms.RealPts.infEmb_unique τ.1 _ _ (hth' k τ) (e ▸ hθ ρ)
  have hN : ∀ k, NegFirst V (X k).p0 fun ρ => x₀ (tauE D ρ) := fun k =>
    negFirst_of_orth V (X k) (hW k) (fun ρ => (hΨ k _).2 ⟨ρ, rfl⟩) x₀ (hO k)
  have hL' : ∀ h k (y : Frame (X k).Ψ V.rank), dict h = ⟨k, y⟩ → ∃ γ ∈ GQ V, ∀ ρ (τ : (X k).Ψ), τ.1 = tauE D ρ →
      mat y τ = archM V (θ ρ) (γ * h) * x₀ (tauE D ρ) := by
    intro h k y e
    have := hL h
    rw [e] at this
    obtain ⟨γ, hγ, H⟩ := this
    refine ⟨γ, hγ, fun ρ τ eτ => ?_⟩
    have := H τ
    rw [hre, e2 k τ ρ eτ, eτ] at this
    exact this
  have hmul' : ∀ g k (y : Frame (X k).Ψ V.rank), dict g = ⟨k, y⟩ → ∀ u ∈ GinfC V, ∃ γ' ∈ (X k).Γ,
      dict (g * u) = ⟨k, lact γ' (rmul y (archMat V th rfl x0 u k))⟩ := by
    intro g k y e u hu
    have := hmul g u hu
    rw [e] at this
    exact this
  have hA : ∀ k (τ : (X k).Ψ) ρ, τ.1 = tauE D ρ → ∀ u, mat (archMat V th rfl x0 u k) τ =
      (mat (x0 k) τ)⁻¹ * archM V (θ ρ) u * mat (x0 k) τ := by
    intro k τ ρ e u
    rw [← e1 k τ ρ e]
    rfl
  have hcen : ∀ k (τ : (X k).Ψ) ρ, τ.1 = tauE D ρ → ∀ u, mat (archMat V th rfl x0 u k) τ =
      (x₀ (tauE D ρ))⁻¹ * archM V (θ ρ) u * x₀ (tauE D ρ) := by
    intro k τ ρ e
    obtain ⟨g0, hg0⟩ := (hx0 k).2
    obtain ⟨γ0, hγ0, H0⟩ := hL' g0 k _ hg0
    have H0' := H0 ρ τ e
    set a := archM V (θ ρ) (γ0 * g0) with ha
    set x := x₀ (tauE D ρ) with hx
    have hxu : IsUnit x.det := (hN k).det_unit ρ
    have hau : IsUnit a.det := archM_det_unit _ _ _
    have haxu : IsUnit (a * x).det := by rw [Matrix.det_mul]; exact hau.mul hxu
    haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
    haveI : Countable (Matrix (Fin V.rank) (Fin V.rank) D.host.E) :=
      inferInstanceAs (Countable (Fin V.rank → Fin V.rank → D.host.E))
    have hc : ∀ w, w * a = a * w := by
      refine GlobalTheory.central_of_countable_commutators_unitary V.rank (gramAt D V ρ) a
        (Set.range fun M : Matrix (Fin V.rank) (Fin V.rank) D.host.E => M.map (tauE D ρ))
        (GlobalTheory.SmoothForms.RealPts.gramAt_herm V ρ) (GlobalTheory.SmoothForms.RealPts.gramAt_unit V ρ) hau
        (Set.countable_range _) fun Z hZ t => ?_
      have hZ' : Zᴴ * gramAt D V ρ + gramAt D V ρ * Z = 0 := hZ
      have hU : NormedSpace.exp (t • Z) ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ) := by
        refine exp_unitary_of_lie (GlobalTheory.SmoothForms.RealPts.gramAt_unit V ρ) ?_
        rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hZ', smul_zero]
      obtain ⟨u, hu, huU⟩ := (GlobalTheory.SmoothForms.RealPts.glue θ hθ V).2
        (fun ρ' => if ρ' = ρ then NormedSpace.exp (t • Z) else 1) (fun ρ' => by
          by_cases h : ρ' = ρ
          · subst h; simpa using hU
          · simp [h, Formalism.QuantumDeterminants.UH])
      have hUu : archM V (θ ρ) u = NormedSpace.exp (t • Z) := by
        have := huU ρ
        rw [if_pos rfl] at this
        exact this
      have hinv : NormedSpace.exp (t • Z) * NormedSpace.exp (-(t • Z)) = 1 := by
        rw [← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Z)).neg_right]
        simp
      generalize NormedSpace.exp (t • Z) = U at hUu hinv
      generalize NormedSpace.exp (-(t • Z)) = U' at hinv
      obtain ⟨γ', -, h1⟩ := hmul' g0 k _ hg0 u hu
      obtain ⟨γ'', hγ'', h2⟩ := hL' _ k _ h1
      have h3 := h2 ρ τ e
      obtain ⟨δ, hδ⟩ := archM_rational V (γ'' * γ0⁻¹) (mul_mem hγ'' (inv_mem hγ0))
      have h4 : γ'' * (g0 * u) = (γ'' * γ0⁻¹) * (γ0 * g0) * u := by group
      rw [h4, archM_mul', archM_mul', hδ _ _ (hθ ρ), ← ha, hUu] at h3
      change γ'.1.map τ.1 * (mat (x0 k) τ * mat (archMat V th rfl x0 u k) τ) = _ at h3
      rw [hA k τ ρ e, H0', hUu, e, ← Matrix.mul_assoc (a * x), ← Matrix.mul_assoc (a * x),
        Matrix.mul_nonsing_inv _ haxu, Matrix.one_mul, ← hx] at h3
      have h5 : γ'.1.map (tauE D ρ) * (U * a) = δ.1.map (tauE D ρ) * a * U := by
        have := congrArg (· * x⁻¹) h3
        simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hxu, Matrix.mul_one] using this
      refine ⟨(γ'⁻¹).1 * δ.1, ?_⟩
      have h6 : (γ'⁻¹).1.map (tauE D ρ) * γ'.1.map (tauE D ρ) = 1 := by
        rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      show ((γ'⁻¹).1 * δ.1).map (tauE D ρ) = _
      rw [Matrix.map_mul, ← Matrix.one_mul (U * a), ← h6, Matrix.mul_assoc _ _ (U * a), h5]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc U, hinv, Matrix.one_mul, Matrix.mul_nonsing_inv _ hau, Matrix.mul_one]
    intro u
    rw [hA k τ ρ e, H0', Matrix.mul_inv_rev, Matrix.mul_assoc x⁻¹, Matrix.mul_assoc x⁻¹, Matrix.mul_assoc x⁻¹,
      Matrix.mul_assoc a⁻¹, ← Matrix.mul_assoc _ a, hc, Matrix.mul_assoc a, ← Matrix.mul_assoc a⁻¹,
      Matrix.nonsing_inv_mul _ hau, Matrix.one_mul]
  refine ⟨fun ρ => x₀ (tauE D ρ), fun k => ⟨⟨hΨ k, hW k⟩, hN k, ?_⟩, fun h => ?_, hfib⟩
  · obtain ⟨g, hg⟩ := (hx0 k).2
    exact ⟨g, by rw [hg]⟩
  · obtain ⟨γ, hγ, H⟩ := hL' h (dict h).1 (dict h).2 rfl
    refine ⟨γ, hγ, fun ρ τ e => H ρ τ e, fun u hu => ?_⟩
    obtain ⟨γ', hγ', h1⟩ := hmul h u hu
    refine ⟨γ', hγ', _, h1, fun ρ τ e => ?_⟩
    change mat (dict h).2 τ * mat (archMat V th rfl x0 u (dict h).1) τ =
      archM V (θ ρ) (γ * h * u) * x₀ (tauE D ρ)
    rw [hcen _ τ ρ e, H ρ τ e, archM_mul' V _ (γ * h) u]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (x₀ _), Matrix.mul_nonsing_inv _ ((hN (dict h).1).det_unit ρ), Matrix.one_mul]

theorem baseDict_core : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ θ : InfFam D, IsInfFam θ → ∃ (hr : (T.V j σ).rank = D.R.r) (x₀ : D.what₂.Tau → Matrix (Fin (T.V j σ).rank) (Fin (T.V j σ).rank) ℂ), BaseDict θ (T.V j σ) hr (T.U j σ).X (T.dict j σ) (T.Kf j σ) x₀ := by
  intro D T h j hj σ hσ θ hθ
  obtain ⟨th, hr, hth, hD⟩ := h.dictU j hj σ hσ
  obtain ⟨hr', hW⟩ := h.modelW j hj σ hσ
  obtain ⟨hr'', g, e, F, ik, φ, th', -, -, hth', -, hL⟩ := h.adPin j hj σ hσ
  have hU := (h.unf j hj σ hσ).2.1
  have hin : ∀ k ρ, tauE D ρ ∈ ((T.U j σ).X k).Ψ := fun k ρ => ((hU k).2 _).2 (h.pins.1.2.2.2 ρ)
  refine ⟨hr, baseDict_of_frames _ hr _ _ _ θ hθ th th' hth hth' (T.x₀ j σ) (fun k τ => ⟨fun hτ => ?_, ?_⟩) hW
    (h.familyUniformisationBasePointOrthogonal j hj σ hσ) hD fun g => ?_⟩
  · obtain ⟨ρ, hρ⟩ := (GlobalTheory.SmoothForms.RealPts.tauE_cm D τ).2 (by
      rintro ⟨ρ, hρ⟩
      exact (((T.U j σ).X k).cmType τ).1 hτ (hρ ▸ hin k ρ))
    exact ⟨ρ, hρ.symm⟩
  · rintro ⟨ρ, rfl⟩
    exact hin k ρ
  · obtain ⟨γ, hγ, -, -, H⟩ := hL g
    exact ⟨γ, hγ, H⟩

end GlobalTheory.HolRead
end

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_dictionary_exists_good_embedding : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ θ : InfFam D, IsInfFam θ → ∃ (hr : (T.V j σ).rank = D.R.r) (x₀ : D.what₂.Tau → Matrix (Fin (T.V j σ).rank) (Fin (T.V j σ).rank) ℂ), BaseDict θ (T.V j σ) hr (T.U j σ).X (T.dict j σ) (T.Kf j σ) x₀ := by
  atlas_forward_decl GlobalTheory.HolRead.baseDict_core
end

section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_form_frame_expansion : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (r : ℕ) (hr : V.rank = r) (X : Data D.host.E r) (x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (w : D.what₂.Tau → Fin V.rank → ℤ) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (φ : GA D V → ℂ), IsInfFam θ → ModelOf V hr X → NegFirst V X.p0 x → (∀ (ρ : D.what₂.Tau) (τ : X.Ψ), τ.1 = tauE D ρ → ∀ c : Fin V.rank, la τ (Fin.cast hr c) = w ρ c) → IsHolFor θ V x w φ → ∀ g : GA D V, ∃ Q : Frame X.Ψ r → ℂ, DifferentiableOn ℂ Q X.dom ∧ (∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Q (rmul y b) = bchar la b * Q y) ∧ ∀ u ∈ GinfC V, ∀ y, FrIs θ V hr X x u y → Q y = φ (g * u) := by
  first | exact @GlobalTheory.HolRead.AdExt.exists_extension | exact GlobalTheory.HolRead.AdExt.exists_extension | (intros; apply GlobalTheory.HolRead.AdExt.exists_extension <;> assumption)
end

section
section
open Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits
  ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.FactorialDivisibilityBounds

noncomputable section

namespace GlobalTheory.SepCusp

theorem exists_threshold {r : ℕ} (p : ℕ) (w : Fin r → ℤ)
    (h : ∀ a b : Fin r, (a : ℕ) < p → p ≤ (b : ℕ) → w a < w b) :
    ∃ M : ℤ, (∀ a : Fin r, (a : ℕ) < p → w a ≤ M) ∧ ∀ b : Fin r, p ≤ (b : ℕ) → M + 1 ≤ w b := by
  classical
  by_cases hne : (Finset.univ.filter fun b : Fin r => p ≤ (b : ℕ)).Nonempty
  · obtain ⟨b0, hb0, hmin⟩ := Finset.exists_min_image _ w hne
    refine ⟨w b0 - 1, fun a ha => ?_, fun b hb => ?_⟩
    · have := h a b0 ha (Finset.mem_filter.mp hb0).2
      omega
    · have := hmin b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
      omega
  · obtain ⟨M, hM⟩ := (Set.finite_range w).bddAbove
    exact ⟨M, fun a _ => hM ⟨a, rfl⟩,
      fun b hb => absurd ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩⟩ hne⟩

theorem sum_le_of_unimodal (a L : ℕ → ℝ) (p r : ℕ) (hp : p ≤ r) (M : ℝ) (h0 : L 0 = 0) (hr : L r = 0)
    (hup : ∀ k < p, L k ≤ L (k + 1)) (hdown : ∀ k, p ≤ k → k < r → L (k + 1) ≤ L k)
    (ha : ∀ k < p, a k ≤ M) (hb : ∀ k, p ≤ k → k < r → M + 1 / 2 ≤ a k) :
    ∑ k ∈ Finset.range r, a k * (L (k + 1) - L k) ≤ -(1 / 2) * L p := by
  rw [← Finset.sum_range_add_sum_Ico _ hp]
  have h1 : ∑ k ∈ Finset.range p, a k * (L (k + 1) - L k) ≤
      ∑ k ∈ Finset.range p, M * (L (k + 1) - L k) :=
    Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right (ha k (Finset.mem_range.mp hk))
      (sub_nonneg.mpr (hup k (Finset.mem_range.mp hk)))
  have h2 : ∑ k ∈ Finset.Ico p r, a k * (L (k + 1) - L k) ≤
      ∑ k ∈ Finset.Ico p r, (M + 1 / 2) * (L (k + 1) - L k) :=
    Finset.sum_le_sum fun k hk => mul_le_mul_of_nonpos_right
      (hb k (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2)
      (sub_nonpos.mpr (hdown k (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2))
  rw [← Finset.mul_sum, Finset.sum_range_sub, h0] at h1
  rw [← Finset.mul_sum, Finset.sum_Ico_sub L hp, hr] at h2
  linarith

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ} (X : Data E r)

theorem rfac_le_of_sep (e : X.Ψ → Fin r → ℂ) (he : X.IsIsoV e) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (s : X.Ψ → ℂ) (hT : X.flowV e s x ∈ X.dom) (τ : X.Ψ) (la : Wt X.Ψ r) (hs : 0 ≤ (s τ).im)
    (hsep : ∀ a b : Fin r, (a : ℕ) < X.p0 → X.p0 ≤ (b : ℕ) → la τ a < la τ b) :
    rfac X la x (X.flowV e s x) τ ≤
      Real.exp (-(1 / 2) * Real.log (1 + (s τ).im / X.ttV e x τ)) := by
  rw [rfac_eq X e he hx s hT τ la]
  apply Real.exp_le_exp.mpr
  have hρ := rho_pos X e he hx s hT τ
  have hsg := hsg_of X hx τ
  have hb : 0 ≤ 2 * X.c τ * (s τ).im := by have := c_pos X τ; positivity
  have hp := X.p0_le
  set L : ℕ → ℝ := fun i => Real.log (rho X e s x τ i) with hLdef
  have hL0 : L 0 = 0 := by simp [L, rho, mN_zero]
  have hLr : L r = 0 := by
    simp [L, rho, mN_top (hG_of X τ) X.p0 (mat x τ) (hx τ).1 hsg (e τ) (he τ).1]
  have hup : ∀ k < X.p0, L k ≤ L (k + 1) := fun k hk => by
    apply Real.log_le_log (hρ k (by omega))
    simp only [rho]
    have := mN_up (hG_of X τ) X.p0 X.p0_le (mat x τ) hsg (e τ) (k + 1) hk k (Nat.le_succ k)
    nlinarith
  have hdown : ∀ k, X.p0 ≤ k → k < r → L (k + 1) ≤ L k := fun k hk hkr => by
    apply Real.log_le_log (hρ (k + 1) hkr)
    simp only [rho]
    have := mN_down (hG_of X τ) X.p0 (mat x τ) hsg (e τ) k hk (k + 1) (Nat.le_succ k) hkr
    nlinarith
  set a : ℕ → ℝ := fun k => if h : k < r then (la τ ⟨k, h⟩ : ℝ) / 2 else 0 with ha
  have hsum : ∑ i : Fin r, (la τ i : ℝ) / 2 *
      (Real.log (rho X e s x τ ((i : ℕ) + 1)) - Real.log (rho X e s x τ i)) =
      ∑ k ∈ Finset.range r, a k * (L (k + 1) - L k) := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => a k * (L (k + 1) - L k)) r]
    exact Finset.sum_congr rfl fun i _ => by simp only [a, L, dif_pos i.2]
  obtain ⟨M, hM1, hM2⟩ := exists_threshold X.p0 (la τ) hsep
  have hq : 1 + (s τ).im / X.ttV e x τ = rho X e s x τ X.p0 := by
    rw [Data.ttV, maj_eq X hx e τ (he τ).1, div_div_eq_mul_div, div_one]
    simp only [rho]
    ring
  rw [hsum, hq]
  refine sum_le_of_unimodal a L X.p0 r hp ((M : ℝ) / 2) hL0 hLr hup hdown (fun k hk => ?_)
    (fun k hk hkr => ?_)
  · have hkr : k < r := by omega
    have h1 : (la τ ⟨k, hkr⟩ : ℝ) ≤ M := by exact_mod_cast hM1 ⟨k, hkr⟩ hk
    simp only [a, dif_pos hkr]
    linarith
  · have h1 : (M : ℝ) + 1 ≤ la τ ⟨k, hkr⟩ := by exact_mod_cast hM2 ⟨k, hkr⟩ hk
    simp only [a, dif_pos hkr]
    linarith

theorem mem_SS_of_sep_at (la : Wt X.Ψ r) (τ0 : X.Ψ) (P : Frame X.Ψ r → ℂ) (hP : X.IsBddSec la P)
    (hsep : ∀ a b : Fin r, (a : ℕ) < X.p0 → X.p0 ≤ (b : ℕ) → la τ0 a < la τ0 b) :
    P ∈ X.SS la := by
  classical
  refine ⟨hP, fun ξ hξ x hx => ?_⟩
  obtain ⟨C, hC⟩ := hP.2
  have hiso : X.IsIsoV (X.embV ξ) := fun τ =>
    ⟨by rw [show X.embV ξ τ = Data.emb τ.1 ξ from rfl, hermC_emb, hξ.2.1, map_zero],
      emb_ne_zero τ.1 hξ.2.2⟩
  set G := X.fj la ξ 0 P with hG
  have hGb : ∀ y ∈ X.dom, ‖G y‖ * X.nfac la y ≤ C := fun y hy =>
    FlowCoefficientBounds.fj_bound X la P C hC hξ 0 hy
  have hGd : DifferentiableOn ℂ G X.dom := CuspCoefficientFlow.fj_diffOn X la P hP hξ 0
  have hreal : ∀ s : X.Ψ → ℝ, G (X.flowV (X.embV ξ) (fun τ => (s τ : ℂ)) x) =
      cexp (4 * Real.pi * I * ∑ τ, (0 : X.Ψ → ℂ) τ * s τ) * G x := by
    intro s
    have := X.fj_flow_real la ξ hξ 0 P hP.1 ⟨C, hC⟩ x hx s
    simp only [Pi.zero_apply, Complex.ofReal_zero, zero_mul] at this ⊢
    exact this
  have hcx := holomorphic_periodicity_extension r X (X.embV ξ) hiso G hGd 0 x hx hreal
  by_contra hne
  have hN := FlowCoefficientBounds.nfac_pos X hx la
  have hA : 0 < ‖G x‖ * X.nfac la x := mul_pos (norm_pos_iff.mpr hne) hN
  have hmaj := maj_eq X hx (X.embV ξ) τ0 (hiso τ0).1
  have hmpos := mN_pos (hG_of X τ0) X.p0 X.p0_le (mat x τ0) (hx τ0).1 (hsg_of X hx τ0)
    (X.embV ξ τ0) (hiso τ0).1 (hiso τ0).2
  have htt : 0 < X.ttV (X.embV ξ) x τ0 := by
    rw [Data.ttV, hmaj]
    have := c_pos X τ0
    positivity
  set M : ℝ := |Real.log (C / (‖G x‖ * X.nfac la x))| + 1 with hM
  have hM0 : 0 < M := by positivity
  set t : ℝ := X.ttV (X.embV ξ) x τ0 * (Real.exp (2 * M) - 1) with ht
  have ht0 : 0 < t := mul_pos htt (by linarith [Real.add_one_lt_exp (show (2 * M) ≠ 0 by positivity)])
  let s : X.Ψ → ℂ := fun τ => if τ = τ0 then I * t else 0
  have hs0 : (s τ0).im = t := by simp [s]
  have hdom : X.flowV (X.embV ξ) s x ∈ X.dom := by
    refine (flowDomainCriterion_holds r X _ hiso x hx s).1.mpr fun τ => ?_
    by_cases h : τ = τ0
    · subst h
      rw [hs0]
      have : 0 < t / X.ttV (X.embV ξ) x τ := div_pos ht0 htt
      linarith
    · simp [s, h]
  have hq : 1 + (s τ0).im / X.ttV (X.embV ξ) x τ0 = Real.exp (2 * M) := by
    rw [hs0, ht, mul_div_cancel_left₀ _ htt.ne']
    ring
  have hratio : X.nfac la x / X.nfac la (X.flowV (X.embV ξ) s x) ≤ Real.exp (-M) := by
    rw [nfac_div, Finset.prod_eq_single τ0 (fun τ _ hτ => rfac_of_zero X _ hiso hx s hdom τ la
      (by simp [s, hτ])) (fun h => absurd (Finset.mem_univ τ0) h)]
    refine (rfac_le_of_sep X _ hiso hx s hdom τ0 la (by rw [hs0]; exact ht0.le) hsep).trans
      (le_of_eq ?_)
    rw [hq, Real.log_exp]
    congr 1
    ring
  have hNT := FlowCoefficientBounds.nfac_pos X hdom la
  have hGT : G (X.flowV (X.embV ξ) s x) = G x := by
    rw [hcx s hdom]
    simp
  have h1 : X.nfac la x ≤ X.nfac la (X.flowV (X.embV ξ) s x) * Real.exp (-M) := by
    rw [div_le_iff₀ hNT] at hratio
    rw [mul_comm]
    exact hratio
  have h2 : ‖G x‖ * X.nfac la x ≤ C * Real.exp (-M) := by
    calc ‖G x‖ * X.nfac la x ≤ ‖G x‖ * (X.nfac la (X.flowV (X.embV ξ) s x) * Real.exp (-M)) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = (‖G (X.flowV (X.embV ξ) s x)‖ * X.nfac la (X.flowV (X.embV ξ) s x)) *
          Real.exp (-M) := by rw [hGT]; ring
      _ ≤ C * Real.exp (-M) := mul_le_mul_of_nonneg_right (hGb _ hdom) (Real.exp_pos _).le
  rcases le_or_gt C 0 with hC0 | hC0
  · have : C * Real.exp (-M) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC0 (Real.exp_pos _).le
    linarith
  · have hlt : Real.log (C / (‖G x‖ * X.nfac la x)) < M := by
      have := le_abs_self (Real.log (C / (‖G x‖ * X.nfac la x)))
      linarith
    have h3 : C / (‖G x‖ * X.nfac la x) < Real.exp M := by
      rw [← Real.exp_log (div_pos hC0 hA)]
      exact Real.exp_lt_exp.mpr hlt
    have h4 : C * Real.exp (-M) < ‖G x‖ * X.nfac la x := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ (Real.exp_pos _)]
      rw [div_lt_iff₀ hA] at h3
      linarith
    linarith

theorem nonempty_type : Nonempty X.Ψ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases h : NumberField.ComplexEmbedding.conjugate τ ∈ X.Ψ
  · exact ⟨⟨_, h⟩⟩
  · exact ⟨⟨τ, (X.cmType τ).mpr h⟩⟩

theorem mem_SS_of_sep (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (r : ℕ) (X : Data E r)
    (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsBddSec la P)
    (hsep : ∀ (τ : X.Ψ) (a b : Fin r), (a : ℕ) < X.p0 → X.p0 ≤ (b : ℕ) → la τ a < la τ b) :
    P ∈ X.SS la := by
  obtain ⟨τ0⟩ := nonempty_type X
  exact mem_SS_of_sep_at X la τ0 P hP (hsep τ0)

end GlobalTheory.SepCusp
end
end

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_section_in_span_of_gap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), X.IsBddSec la P → (∀ (τ : X.Ψ) (a b : Fin r), (a : ℕ) < X.p0 → X.p0 ≤ (b : ℕ) → la τ a < la τ b) → P ∈ X.SS la := by
  atlas_forward_decl GlobalTheory.SepCusp.mem_SS_of_sep
end

section
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.Descent

theorem lact_mul {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (γ γ' : GL (Fin r) E) (x : Frame Ψ r) :
    lact (γ * γ') x = lact γ (lact γ' x) := by
  funext τ
  show ((γ * γ' : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ =
    (γ : Matrix (Fin r) (Fin r) E).map τ.1 * ((γ' : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ)
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

theorem lact_rmul {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (γ : GL (Fin r) E) (x b : Frame Ψ r) :
    lact γ (rmul x b) = rmul (lact γ x) b := by
  funext τ
  show (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * mat b τ) =
    ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) * mat b τ
  rw [Matrix.mul_assoc]

theorem archM_mul {D : D7} (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (a b : GA D V) :
    archM V θ (a * b) = archM V θ a * archM V θ b := by
  simp only [archM, map_mul, Units.val_mul, Matrix.map_mul]

theorem isUnit_of_negFirst {D : D7} {V : HSp D} {q : ℕ} {x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (h : NegFirst V q x) (ρ : D.what₂.Tau) : IsUnit (x ρ) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro h0
  have h1 := congrArg Matrix.det (h ρ)
  rw [Matrix.det_mul, h0, mul_zero, Matrix.det_diagonal] at h1
  refine (Finset.prod_ne_zero_iff.2 fun c _ => ?_) h1.symm
  split_ifs <;> simp

theorem archM_eq_of_frIs {D : D7} {θ : InfFam D} {V : HSp D} {r : ℕ} {hr : V.rank = r} {X : Data D.host.E r}
    {x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} (hM : ModelOf V hr X) (hx : NegFirst V X.p0 x)
    {u u' : GA D V} {y : Frame X.Ψ r} (h : FrIs θ V hr X x u y) (h' : FrIs θ V hr X x u' y) (ρ : D.what₂.Tau) :
    archM V (θ ρ) u = archM V (θ ρ) u' := by
  have e := (h ρ ⟨tauE D ρ, (hM.1 _).2 ⟨ρ, rfl⟩⟩ rfl).symm.trans (h' ρ ⟨tauE D ρ, (hM.1 _).2 ⟨ρ, rfl⟩⟩ rfl)
  exact (isUnit_of_negFirst hx ρ).mul_right_cancel ((Matrix.reindex _ _).injective e)

theorem descent : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (r : ℕ) (hr : V.rank = r) (Comp : Type) (X : Comp → Data D.host.E r) (dict : GA D V → Σ k, Frame (X k).Ψ r) (Kf : Subgroup (GA D V)) (x₀ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (ψ : GA D V → ℂ), IsInfFam θ → BaseDict θ V hr X dict Kf x₀ → (∀ k, ∀ γ ∈ (X k).Γ, (X k).χ (la k) γ = 1) → (∀ γ ∈ GQ V, ∀ g, ψ (γ * g) = ψ g) → (∀ k ∈ Kf, ∀ g, ψ (g * k) = ψ g) → (∀ (k : Comp) (g : GA D V), ∃ Q : Frame (X k).Ψ r → ℂ, DifferentiableOn ℂ Q (X k).dom ∧ (∀ y ∈ (X k).dom, ∀ b ∈ Bor (X k).Ψ r, Q (rmul y b) = bchar (la k) b * Q y) ∧ ∀ u ∈ GinfC V, ∀ y, FrIs θ V hr (X k) x₀ u y → Q y = ψ (g * u)) → ∃ P : FDSec X, (∀ k, (X k).IsSec (la k) (P k)) ∧ (∀ g, ψ g = P (dict g).1 (dict g).2) ∧ ∀ C : ℝ, (∀ g, ‖ψ g‖ ≤ C) → ∀ k, ∀ y ∈ (X k).dom, (X k).pnorm (la k) (P k) y ≤ C := by
  intro D θ V r hr Comp X dict Kf x₀ la ψ hθ hB hχ hL hR hQ
  obtain ⟨hB1, hB2, hB3⟩ := hB
  have hF : ∀ (k : Comp) (h h' : GA D V) (z : Frame (X k).Ψ r), ∀ γ ∈ (X k).Γ,
      dict h = ⟨k, z⟩ → dict h' = ⟨k, lact γ z⟩ → ψ h' = ψ h := by
    intro k h h' z γ hγ e e'
    have key : ∀ p : Σ k, Frame (X k).Ψ r, p = ⟨k, z⟩ →
        ∃ γ' ∈ (X p.1).Γ, dict h' = ⟨p.1, lact γ' p.2⟩ := by
      rintro p rfl
      exact ⟨γ, hγ, e'⟩
    obtain ⟨δ, hδ, κ, hκ, rfl⟩ := hB3 h h' (key _ e)
    rw [hR κ hκ, hL δ hδ]
  have hK : ∀ k : Comp, ∃ Q : Frame (X k).Ψ r → ℂ, DifferentiableOn ℂ Q (X k).dom ∧
      (∀ y ∈ (X k).dom, ∀ b ∈ Bor (X k).Ψ r, Q (rmul y b) = bchar (la k) b * Q y) ∧
      ∀ y, IsUnitFr (X k) y → ∃ h, ∃ γ ∈ (X k).Γ, dict h = ⟨k, lact γ y⟩ ∧ Q y = ψ h := by
    intro k
    obtain ⟨hM, hN, g, rfl⟩ := hB1 k
    obtain ⟨U1, U2, -, U4, -⟩ := GlobalTheory.T.frame_unit_correspondence D θ V r hr (X (dict g).1) x₀ hθ hM hN
    obtain ⟨γ, hγ, hfr, hu⟩ := hB2 g
    obtain ⟨a, ha, hfa⟩ := U2 _ (U1 _ _ hfr)
    have ea := archM_eq_of_frIs hM hN hfr hfa
    obtain ⟨Q, hQ1, hQ2, hQ3⟩ := hQ (dict g).1 (γ * g * a⁻¹)
    refine ⟨Q, hQ1, hQ2, fun y hy => ?_⟩
    obtain ⟨v, hv, hfv⟩ := U2 y hy
    obtain ⟨γ', hγ', y', hd, hfy'⟩ := hu (a⁻¹ * v) (mul_mem (inv_mem ha) hv)
    have hfy : FrIs θ V hr (X (dict g).1) x₀ v y' := by
      intro ρ τ hτ
      rw [hfy' ρ τ hτ, archM_mul V _ (γ * g), ea ρ, ← archM_mul, mul_inv_cancel_left]
    obtain rfl : y' = y := U4 v _ _ hfy hfv
    refine ⟨_, γ', hγ', hd, ?_⟩
    rw [hQ3 v hv _ hfv, ← hL γ hγ (g * (a⁻¹ * v))]
    simp only [mul_assoc]
  choose P hP1 hP2 hP3 using hK
  refine ⟨P, fun k => ⟨hP1 k, hP2 k, fun γ hγ x hx => ?_⟩, fun g => ?_, fun C hC k x hx => ?_⟩
  · obtain ⟨G1, G2, -, -, G5, -⟩ := GlobalTheory.T.gramSchmidt_flagDomain_orthonormalFrames D.host.E r (X k)
    obtain ⟨y, hy, b, hb, rfl⟩ := G2 x hx
    have hy' := G5 y hy γ hγ
    obtain ⟨h, γ₁, hγ₁, hd, he⟩ := hP3 k y hy
    obtain ⟨h', γ₂, hγ₂, hd', he'⟩ := hP3 k _ hy'
    have e : ψ h' = ψ h := by
      refine hF k h h' _ (γ₂ * γ * γ₁⁻¹) (mul_mem (mul_mem hγ₂ hγ) (inv_mem hγ₁)) hd ?_
      rw [hd', ← lact_mul, ← lact_mul, inv_mul_cancel_right]
    rw [hχ k γ hγ, one_mul, lact_rmul, hP2 k _ (G1 _ hy') b hb, hP2 k _ (G1 _ hy) b hb, he, he', e]
  · obtain ⟨hM, hN, -⟩ := hB1 (dict g).1
    obtain ⟨U1, -⟩ := GlobalTheory.T.frame_unit_correspondence D θ V r hr (X (dict g).1) x₀ hθ hM hN
    obtain ⟨γ, -, hfr, -⟩ := hB2 g
    obtain ⟨h, γ₁, hγ₁, hd, he⟩ := hP3 _ _ (U1 _ _ hfr)
    rw [he]
    exact (hF _ g h _ γ₁ hγ₁ rfl hd).symm
  · obtain ⟨G1, G2, -, -, -, -, G7⟩ := GlobalTheory.T.gramSchmidt_flagDomain_orthonormalFrames D.host.E r (X k)
    obtain ⟨y, hy, b, hb, rfl⟩ := G2 x hx
    rw [G7 (la k) (P k) y hy b hb (hP2 k y (G1 y hy) b hb)]
    obtain ⟨h, -, -, -, he⟩ := hP3 k y hy
    rw [he]
    exact hC h

end GlobalTheory.HolRead.Descent
end

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphic_expansion_in_dictionary : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (r : ℕ) (hr : V.rank = r) (Comp : Type) (X : Comp → Data D.host.E r) (dict : GA D V → Σ k, Frame (X k).Ψ r) (Kf : Subgroup (GA D V)) (x₀ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (ψ : GA D V → ℂ), IsInfFam θ → BaseDict θ V hr X dict Kf x₀ → (∀ k, ∀ γ ∈ (X k).Γ, (X k).χ (la k) γ = 1) → (∀ γ ∈ GQ V, ∀ g, ψ (γ * g) = ψ g) → (∀ k ∈ Kf, ∀ g, ψ (g * k) = ψ g) → (∀ (k : Comp) (g : GA D V), ∃ Q : Frame (X k).Ψ r → ℂ, DifferentiableOn ℂ Q (X k).dom ∧ (∀ y ∈ (X k).dom, ∀ b ∈ Bor (X k).Ψ r, Q (rmul y b) = bchar (la k) b * Q y) ∧ ∀ u ∈ GinfC V, ∀ y, FrIs θ V hr (X k) x₀ u y → Q y = ψ (g * u)) → ∃ P : FDSec X, (∀ k, (X k).IsSec (la k) (P k)) ∧ (∀ g, ψ g = P (dict g).1 (dict g).2) ∧ ∀ C : ℝ, (∀ g, ‖ψ g‖ ≤ C) → ∀ k, ∀ y ∈ (X k).dom, (X k).pnorm (la k) (P k) y ≤ C := by
  atlas_forward_decl GlobalTheory.HolRead.Descent.descent
end

section
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.ToHol

theorem det_ne_of_frame {n : ℕ} (q : ℕ) (G x : Matrix (Fin n) (Fin n) ℂ)
    (h : xᴴ * G * x = diagonal fun c : Fin n => if (c : ℕ) < q then (-1 : ℂ) else 1) : x.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det h
  rw [det_mul, h0, mul_zero, det_diagonal] at this
  refine (Finset.prod_ne_zero_iff.2 fun c _ => ?_) this.symm
  split_ifs <;> norm_num

theorem unitary_of_frames {n : ℕ} (G x x₀ : Matrix (Fin n) (Fin n) ℂ) (hx : x.det ≠ 0)
    (h : x₀ᴴ * G * x₀ = xᴴ * G * x) : (x₀ * x⁻¹)ᴴ * G * (x₀ * x⁻¹) = G := by
  have hu : IsUnit x.det := hx.isUnit
  have h1 : x * x⁻¹ = 1 := mul_nonsing_inv x hu
  calc (x₀ * x⁻¹)ᴴ * G * (x₀ * x⁻¹) = x⁻¹ᴴ * (x₀ᴴ * G * x₀) * x⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (x * x⁻¹)ᴴ * G * (x * x⁻¹) := by
        rw [h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = G := by rw [h1]; simp

theorem differentiable_det {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (τ : Ψ) :
    Differentiable ℂ fun y : Frame Ψ r => (mat y τ).det := by
  simp only [det_apply', mat, of_apply]
  fun_prop

theorem bchar_shift {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (la : ReciprocityTheory.ChartRestriction.G.FD.Wt Ψ r) (e : Ψ → ℤ)
    (b : Frame Ψ r) (hb : b ∈ Bor Ψ r) :
    bchar la b = bchar (fun τ i => la τ i - e τ) b * ∏ τ, (mat b τ).det ^ e τ := by
  unfold bchar
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hd : (mat b τ).det = ∏ i, b τ i i :=
    det_of_upperTriangular (M := mat b τ) fun a c h => (hb τ).2 a c h
  have hne : ∀ i, b τ i i ≠ 0 := fun i =>
    Finset.prod_ne_zero_iff.1 (fun h => (hb τ).1 (hd.trans h)) i (Finset.mem_univ _)
  rw [hd, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_add₀ (hne i), sub_add_cancel]

theorem archM_mul' {D : D7} (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (a b : GA D V) :
    archM V θ (a * b) = archM V θ a * archM V θ b := by
  unfold archM
  rw [map_mul, Units.val_mul, Matrix.map_mul]

theorem exists_holCusp : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (r : ℕ) (hr : V.rank = r) (Comp : Type) (X : Comp → Data D.host.E r) (dict : GA D V → Σ k, Frame (X k).Ψ r) (Kf : Subgroup (GA D V)) (x₀ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (q : ℕ) (w : D.what₂.Tau → Fin V.rank → ℤ) (e : D.what₂.Tau → ℤ) (mu : GA D V → ℂ), IsInfFam θ → BaseDict θ V hr X dict Kf x₀ → Kf ≤ GfC V → (∀ k, (X k).p0 = q) → NegFirst V q x → (∀ g g', mu (g * g') = mu g * mu g') → (∀ g, ‖mu g‖ = 1) → (∀ γ ∈ GQ V, mu γ = 1) → (∀ k ∈ Kf, mu k = 1) → (∀ u ∈ GinfC V, mu u = ∏ ρ, (archM V (θ ρ) u).det ^ (-(e ρ))) → (∀ k (ρ : D.what₂.Tau) (τ : (X k).Ψ), τ.1 = tauE D ρ → ∀ c : Fin V.rank, la k τ (Fin.cast hr c) = w ρ c + e ρ) → (∀ k, ∀ γ ∈ (X k).Γ, (X k).χ (la k) γ = 1) → (∀ k (τ : (X k).Ψ) (a b : Fin r), (a : ℕ) < q → q ≤ (b : ℕ) → la k τ a < la k τ b) → ∃ a : GA D V, ∀ φ : GA D V → ℂ, IsHolFor θ V x w φ → (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) → (∀ k ∈ Kf, ∀ g, φ (g * k) = φ g) → (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) → ∃ P : FDSec X, IsHolCusp X la P ∧ ∀ g, φ (g * a) = mu g * P (dict g).1 (dict g).2 := by
  intro D θ V r hr Comp X dict Kf x₀ la x q w e mu hθ hB hKf hq hx hmul hnorm hQ hK hinf hla hχ hsep
  have hx₀ : NegFirst V q x₀ := hq (dict 1).1 ▸ (hB.1 (dict 1).1).2.1
  have hdx : ∀ ρ, (x ρ).det ≠ 0 := fun ρ => det_ne_of_frame q _ _ (hx ρ)
  have hdx₀ : ∀ ρ, (x₀ ρ).det ≠ 0 := fun ρ => det_ne_of_frame q _ _ (hx₀ ρ)
  obtain ⟨a, ha, haM⟩ := (GlobalTheory.SmoothForms.RealPts.glue θ hθ V).2 (fun ρ => x₀ ρ * (x ρ)⁻¹)
    (fun ρ => unitary_of_frames _ _ _ (hdx ρ) ((hx₀ ρ).trans (hx ρ).symm))
  have haM' : ∀ ρ, archM V (θ ρ) a * x ρ = x₀ ρ := fun ρ => by
    have : archM V (θ ρ) a = x₀ ρ * (x ρ)⁻¹ := haM ρ
    rw [this, Matrix.mul_assoc, nonsing_inv_mul _ (hdx ρ).isUnit, Matrix.mul_one]
  have hcomm := (GlobalTheory.UnitarySplit.real_finite_split D V).2.1
  have hmu0 : ∀ g, mu g ≠ 0 := fun g h => by simpa [h] using hnorm g
  refine ⟨a, fun φ hφ hl hk ⟨C, hC⟩ => ?_⟩
  obtain ⟨P, hP, hPe, hPb⟩ := GlobalTheory.T.automorphic_expansion_in_dictionary D θ V r hr Comp X dict Kf x₀ la (fun g => φ (g * a) / mu g) hθ hB hχ
    (fun γ hγ g => by simp only [mul_assoc, hl γ hγ, hmul, hQ γ hγ, one_mul])
    (fun k hk' g => by
      simp only [hmul, hK k hk', mul_one]
      rw [mul_assoc, ← hcomm a ha k (hKf hk'), ← mul_assoc, hk k hk'])
    (fun k g => by
      have hM := (hB.1 k).1
      choose s hs using fun τ : (X k).Ψ => (hM.1 τ.1).1 τ.2
      have hsρ : ∀ (ρ : D.what₂.Tau) (τ : (X k).Ψ), τ.1 = tauE D ρ → s τ = ρ := fun ρ τ h =>
        GlobalTheory.SmoothForms.RealPts.tauE_injective D ((hs τ).symm.trans h)
      have hsb : Function.Bijective s := by
        refine ⟨fun τ τ' h => Subtype.ext (by rw [hs τ, hs τ', h]), fun ρ => ?_⟩
        exact ⟨⟨tauE D ρ, (hM.1 _).2 ⟨ρ, rfl⟩⟩, hsρ ρ _ rfl⟩
      obtain ⟨Q, hQd, hQb, hQe⟩ := GlobalTheory.T.holomorphic_form_frame_expansion D θ V r hr (X k) x w (fun τ i => la k τ i - e (s τ)) φ hθ hM
        ((hq k).symm ▸ hx) (fun ρ τ h c => by simp only [hla k ρ τ h c, hsρ ρ τ h, add_sub_cancel_right]) hφ g
      refine ⟨fun y => Q y * (∏ τ, (mat y τ).det ^ e (s τ)) * ((mu g)⁻¹ * ∏ τ, (x₀ (s τ)).det ^ (-e (s τ))), ?_, ?_, ?_⟩
      · refine DifferentiableOn.mul_const (hQd.mul ?_) _
        intro y hy
        refine DifferentiableAt.differentiableWithinAt ?_
        exact (HasFDerivAt.finset_prod (u := Finset.univ) (g := fun τ (y : Frame (X k).Ψ r) => (mat y τ).det ^ e (s τ))
          fun τ _ => (((differentiable_det τ) y).zpow (Or.inl (hy τ).1)).hasFDerivAt).differentiableAt
      · intro y hy b hb
        have hm : ∀ τ, mat (rmul y b) τ = mat y τ * mat b τ := fun τ => rfl
        simp only [hQb y hy b hb, hm, det_mul, mul_zpow, Finset.prod_mul_distrib]
        rw [bchar_shift (la k) (fun τ => e (s τ)) b hb]
        ring
      · intro u hu y hy
        have hy' : FrIs θ V hr (X k) x (u * a) y := fun ρ τ h => by
          rw [hy ρ τ h, archM_mul', Matrix.mul_assoc, haM']
        have hd : ∀ τ, (mat y τ).det = (archM V (θ (s τ)) u).det * (x₀ (s τ)).det := fun τ => by
          rw [hy (s τ) τ (hs τ), det_reindex_self, det_mul]
        have hu' : mu u = ∏ τ, (archM V (θ (s τ)) u).det ^ (-(e (s τ))) := by
          rw [hinf u hu]
          exact (hsb.prod_comp fun ρ => (archM V (θ ρ) u).det ^ (-(e ρ))).symm
        have h1 : (∏ τ, (x₀ (s τ)).det ^ e (s τ)) * ∏ τ, (x₀ (s τ)).det ^ (-e (s τ)) = 1 := by
          rw [← Finset.prod_mul_distrib]
          exact Finset.prod_eq_one fun τ _ => by rw [← zpow_add₀ (hdx₀ _), add_neg_cancel, zpow_zero]
        have h2 : (∏ τ, (archM V (θ (s τ)) u).det ^ e (s τ)) = (mu u)⁻¹ := by
          rw [hu', ← Finset.prod_inv_distrib]
          exact Finset.prod_congr rfl fun τ _ => by rw [_root_.zpow_neg, inv_inv]
        simp only [hQe (u * a) (mul_mem hu ha) y hy', hd, mul_zpow, Finset.prod_mul_distrib, h2, hmul, mul_assoc g u a]
        rw [div_eq_mul_inv, mul_inv]
        linear_combination (φ (g * (u * a)) * (mu u)⁻¹ * (mu g)⁻¹) * h1)
  refine ⟨P, fun k => ?_, fun g => ?_⟩
  · refine GlobalTheory.T.bounded_section_in_span_of_gap _ r (X k) (la k) (P k) ⟨hP k, C, hPb C (fun g => ?_) k⟩ ?_
    · simpa only [norm_div, hnorm, div_one] using hC _
    · intro τ a b h1 h2
      rw [hq k] at h1 h2
      exact hsep k τ a b h1 h2
  · rw [← hPe g]
    field_simp [hmu0 g]

end GlobalTheory.HolRead.ToHol
end

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_expansion_weight_compat : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (r : ℕ) (hr : V.rank = r) (Comp : Type) (X : Comp → Data D.host.E r) (dict : GA D V → Σ k, Frame (X k).Ψ r) (Kf : Subgroup (GA D V)) (x₀ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (q : ℕ) (w : D.what₂.Tau → Fin V.rank → ℤ) (e : D.what₂.Tau → ℤ) (mu : GA D V → ℂ), IsInfFam θ → BaseDict θ V hr X dict Kf x₀ → Kf ≤ GfC V → (∀ k, (X k).p0 = q) → NegFirst V q x → (∀ g g', mu (g * g') = mu g * mu g') → (∀ g, ‖mu g‖ = 1) → (∀ γ ∈ GQ V, mu γ = 1) → (∀ k ∈ Kf, mu k = 1) → (∀ u ∈ GinfC V, mu u = ∏ ρ, (archM V (θ ρ) u).det ^ (-(e ρ))) → (∀ k (ρ : D.what₂.Tau) (τ : (X k).Ψ), τ.1 = tauE D ρ → ∀ c : Fin V.rank, la k τ (Fin.cast hr c) = w ρ c + e ρ) → (∀ k, ∀ γ ∈ (X k).Γ, (X k).χ (la k) γ = 1) → (∀ k (τ : (X k).Ψ) (a b : Fin r), (a : ℕ) < q → q ≤ (b : ℕ) → la k τ a < la k τ b) → ∃ a : GA D V, ∀ φ : GA D V → ℂ, IsHolFor θ V x w φ → (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) → (∀ k ∈ Kf, ∀ g, φ (g * k) = φ g) → (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) → ∃ P : FDSec X, IsHolCusp X la P ∧ ∀ g, φ (g * a) = mu g * P (dict g).1 (dict g).2 := by
  atlas_forward_decl GlobalTheory.HolRead.ToHol.exists_holCusp
end

section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_character_det_power : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (χ : (AE D)ˣ →* Circle) (mu : GA D V → ℂ) (e : D.what₂.Tau → ℤ), IsInfFam θ → MuVal V χ mu → (∀ ρ, HasInfExp D χ ρ (-(e ρ : ℚ))) → ∀ u ∈ GinfC V, mu u = ∏ ρ, (archM V (θ ρ) u).det ^ (-(e ρ)) := by
  first | exact @GlobalTheory.HolRead.mu_real_eq_prod_det | exact GlobalTheory.HolRead.mu_real_eq_prod_det | (intros; apply GlobalTheory.HolRead.mu_real_eq_prod_det <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_character_trivial_on_subgroup : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → ∀ (i : Fin D.R.m) (Kf : Subgroup (GA D (Wc D i))), IsLevelK (Wc D i) (D.host.g 0 * D.host.g 1) Kf → ∀ k ∈ Kf, k ∈ levS (Wc D i) (L.βW i) (L.datWp i L.triv) ∧ Lev.levChi (Wc D i) (L.βW i) (L.datWp i L.triv) k = 1 := by
  first | exact @GlobalTheory.HolRead.PrincLevelSub.mem_levS_and_levChi | exact GlobalTheory.HolRead.PrincLevelSub.mem_levS_and_levChi | (intros; apply GlobalTheory.HolRead.PrincLevelSub.mem_levS_and_levChi <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.last_weight_positive : ∀ (D : D7) (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), LawsJ T → KapIs κ → ∀ i : Fin D.R.m, LastPos (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) := by
  first | exact @GlobalTheory.HolRead.lastPos_wtA_of_kapIs | exact GlobalTheory.HolRead.lastPos_wtA_of_kapIs | (intros; apply GlobalTheory.HolRead.lastPos_wtA_of_kapIs <;> assumption)
end

section
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead

theorem mu_eq_one_of_mem_level : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), LawsJ T → R.toLevCh.Is A.μ0 → ChiR T R → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ k ∈ T.Kf ((i : ℕ) + 1) (res T σ), T.mu ((i : ℕ) + 1) (res T σ) k = 1 := by
  intro D G _ _ Pl0 T0 A T _ R hT hL hC i σ hσ k hk
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hodd : Odd (D.host.g 0 * D.host.g 1) :=
    ((D.host.g_prime 0).odd_of_ne_two (g_ne_two D 0)).mul ((D.host.g_prime 1).odd_of_ne_two (g_ne_two D 1))
  obtain ⟨hk1, hk2⟩ := (hT.levelK _ hj _ hσ k).1 hk
  obtain ⟨x, hxu, hxr, hxc⟩ := GlobalTheory.UnitDetRoot.exists_unit_detRoot D _ _ hodd k hk1 hk2
  have h0 : R.mu0 ((i : ℕ) + 1) x = 1 := by
    refine GlobalTheory.tame_heckeChar_eq_one_of_finUnit D _ _ (hL.mu0 i) (R.C.isMu0 i).tame _ (fun P hP => ?_) x hxu hxc
    refine (R.C.isMu0 i).unr P fun l hl => hP ?_
    have hl' : ((D.host.g l : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := hl
    rw [Nat.cast_mul]
    fin_cases l
    · exact P.asIdeal.mul_mem_right _ hl'
    · exact P.asIdeal.mul_mem_left _ hl'
  obtain ⟨y, hy1, hy2⟩ := (hC i σ hσ).2.2.2.1 x hxu.1
  rw [h0, Circle.coe_one] at hy1
  have hy : algebraMap T.Q.c.F D.what₂.LL y = 1 :=
    D.what₂.embLL.injective (hy1.symm.trans (map_one _).symm)
  rw [hy, map_one] at hy2
  exact ((hT.muVal _ hj _ hσ).2 k x hxr).trans hy2

end GlobalTheory.HolRead
end

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_character_trivial_on_level : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), LawsJ T → R.toLevCh.Is A.μ0 → ChiR T R → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ k ∈ T.Kf ((i : ℕ) + 1) (res T σ), T.mu ((i : ℕ) + 1) (res T σ) k = 1 := by
  atlas_forward_decl GlobalTheory.HolRead.mu_eq_one_of_mem_level
end

section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_label_at_unfolding : ∀ (D : D7) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), LawsJ T → AlgTie T → KapIs κ → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ (e : D.what₂.Tau → ℤ), (∀ ρ, (e ρ : ℚ) = (D.hc (lab σ ρ)).e i) → ∀ k (ρ : D.what₂.Tau) (τ : ((T.U ((i : ℕ) + 1) (res T σ)).X k).Ψ), τ.1 = tauE D ρ → ∀ c : Fin D.R.r, laU (T.U ((i : ℕ) + 1) (res T σ)) (wtA (κ i)) (κ i).n k τ c = wtCol (D.hc (lab σ ρ)) (D.R.sigW ((i : ℕ) + 1)).1 (D.R.sigW ((i : ℕ) + 1)).2 c + e ρ := by
  first | exact @GlobalTheory.HolRead.SecWt.laU_eq_wtCol | exact GlobalTheory.HolRead.SecWt.laU_eq_wtCol | (intros; apply GlobalTheory.HolRead.SecWt.laU_eq_wtCol <;> assumption)
end

section
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead

open GlobalTheory.HolDict.ModelRep in

theorem isHolFor_extVec_holPar : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (h : D.what₂.Tau → HCParam D.R) (p q : ℕ), IsInfFam θ → p + q = D.R.r → V.rank = D.R.r → (∀ ρ, S ρ = Formalism.L2.NTheta.holPar p q (Formalism.L2.NTheta.kapW (h ρ) p q)) → ∀ v : M.Vec, IsExtVec M v → ∃ x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, NegFirst V q x ∧ ∀ (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsMultMap θ M J χ T → IsHolFor θ V x (fun ρ c => wtCol (h ρ) p q c) (T v) := by
  intro D θ V S M h p q hθ hpq hr hS v hv
  have hn : p + q = V.rank := hpq.trans hr.symm
  have hp : p ≤ V.rank := by omega
  have he : ∀ ρ, IsEnum (Formalism.L2.NTheta.holPar p q (Formalism.L2.NTheta.kapW (h ρ) p q)) (M.lam ρ) (M.ε ρ) :=
    fun ρ => hS ρ ▸ M.enum ρ
  have hok := fun ρ => Formalism.L2.NTheta.holOK_kapW (h ρ) p q hpq
  have hε : ∀ ρ a, M.ε ρ a = decide ((a : ℕ) < p) := fun ρ a => by
    obtain ⟨hn', hx⟩ := GlobalTheory.HolDS.enum_holPar (hok ρ) (he ρ)
    by_cases ha : (a : ℕ) < p
    · have := (hx (Sum.inl ⟨a, ha⟩)).2
      rw [show Fin.cast hn' (finSumFinEquiv (Sum.inl ⟨a, ha⟩ : Fin p ⊕ Fin q)) = a from Fin.ext (by simp)] at this
      simp [this, ha]
    · have := (hx (Sum.inr ⟨a - p, by have := a.2; omega⟩)).2
      rw [show Fin.cast hn' (finSumFinEquiv (Sum.inr ⟨a - p, by have := a.2; omega⟩ : Fin p ⊕ Fin q)) = a from
        Fin.ext (by simp; omega)] at this
      simp [this, ha]
  have hq : ∀ ρ, nNeg (M.ε ρ) = q := fun ρ => by rw [nNeg_shape hp (hε ρ)]; omega
  have hw : ∀ ρ c, extWt M ρ (arr (nNeg (M.ε ρ)) c) = (wtCol (h ρ) p q c : ℝ) := fun ρ c => by
    obtain ⟨hn', hx⟩ := GlobalTheory.HolDS.lowK_holPar (hok ρ) (he ρ)
    have hc := c.2
    by_cases hcq : (c : ℕ) < q
    · rw [extWt_arr M ρ hp (hε ρ) c (Fin.cast hn' (finSumFinEquiv (Sum.inr ⟨c, hcq⟩ : Fin p ⊕ Fin q)))
        (by rw [if_pos (by omega)]; simp), hx]
      simp only [wtCol, if_pos hcq, Formalism.L2.NTheta.kapW, Formalism.L2.NTheta.kapQ, Sum.elim_inr]
    · rw [extWt_arr M ρ hp (hε ρ) c (Fin.cast hn' (finSumFinEquiv (Sum.inl ⟨c - q, by omega⟩ : Fin p ⊕ Fin q)))
        (by rw [if_neg (by omega)]; simp; omega), hx]
      simp only [wtCol, if_neg hcq, Formalism.L2.NTheta.kapW, Formalism.L2.NTheta.kapQ, Sum.elim_inl]
  have hneg : NegFirst V q (x0Mat M) := fun ρ => by
    have := orth_sub (M.fr_unit ρ) (M.fr_gram ρ) (arr (nNeg (M.ε ρ)))
    refine this.trans ?_
    unfold Formalism.REAL.Jm
    rw [Matrix.submatrix_diagonal _ _ (arr_injective (nNeg_le (M.ε ρ)))]
    congr 1
    funext a
    have := a.2
    simp only [Function.comp, hε, hq, arr, decide_eq_true_eq]
    split_ifs <;> first | rfl | (exfalso; simp only at *; omega)
  refine ⟨x0Mat M, hneg, fun J χ T hT => ⟨(hT.aut v).smooth, fun ρ c d hcd => ?_, fun ρ t g => ?_⟩⟩
  · have hk := (GlobalTheory.T.extremal_vector_annihilated D θ V S M J χ T hθ hT v hv ρ p true (fun a => by rw [hε]; by_cases ha : (a : ℕ) < p <;> simp [ha])).1
    have e := conj_single (M.fr_unit ρ) (arrEquiv (nNeg_le (M.ε ρ))) c d
    change x0Mat M ρ * _ * (x0Mat M ρ)⁻¹ =
      _ * Matrix.single (arr (nNeg (M.ε ρ)) c) (arr (nNeg (M.ε ρ)) d) 1 * _ at e
    rw [e]
    apply hk
    have h1 : (c : ℕ) < d := hcd
    have h2 := d.2
    simp only [KillPair, hε, hq, arr, Fin.lt_def, decide_eq_true_eq, decide_eq_false_iff_not, ne_eq, decide_eq_decide]
    split_ifs <;> simp only <;> omega
  · have hk := (GlobalTheory.T.extremal_vector_annihilated D θ V S M J χ T hθ hT v hv ρ p true (fun a => by rw [hε]; by_cases ha : (a : ℕ) < p <;> simp [ha])).2
    set e := arrEquiv (nNeg_le (M.ε ρ)) with hedef
    have hx : IsUnit (x0Mat M ρ).det := by
      have h1 := congrArg Matrix.det (hneg ρ)
      rw [det_mul, det_diagonal] at h1
      refine isUnit_iff_ne_zero.2 fun h0 => ?_
      rw [h0, mul_zero] at h1
      exact Finset.prod_ne_zero_iff.2 (fun a _ => by split_ifs <;> simp) h1.symm
    have h1 := torus_x0Mat M ρ fun a => Complex.exp ((t (e.symm a) : ℂ) * Complex.I)
    have h2 : ∀ c, e.symm (arr (nNeg (M.ε ρ)) c) = c := fun c => e.symm_apply_apply c
    simp only [h2] at h1
    rw [← h1, Matrix.mul_nonsing_inv_cancel_right _ _ hx, hk (fun a => t (e.symm a)) g, ← e.sum_comp]
    simp only [Equiv.symm_apply_apply]
    congr 5
    funext c
    rw [← hw ρ c]
    rfl

end GlobalTheory.HolRead
end

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_extremal_negative_first : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (h : D.what₂.Tau → HCParam D.R) (p q : ℕ), IsInfFam θ → p + q = D.R.r → V.rank = D.R.r → (∀ ρ, S ρ = Formalism.L2.NTheta.holPar p q (Formalism.L2.NTheta.kapW (h ρ) p q)) → ∀ v : M.Vec, IsExtVec M v → ∃ x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, NegFirst V q x ∧ ∀ (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsMultMap θ M J χ T → IsHolFor θ V x (fun ρ c => wtCol (h ρ) p q c) (T v) := by
  atlas_forward_decl GlobalTheory.HolRead.isHolFor_extVec_holPar
end

section
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.AntiHol

theorem isEnum_dual {n : ℕ} {S : SPar} {lam : Fin n → ℝ} {ε : Fin n → Bool} (he : IsEnum (dualPar S) lam ε) :
    IsEnum S (fun a => -lam (Fin.rev a)) (fun a => ε (Fin.rev a)) := by
  obtain ⟨hl, r, hr, hS⟩ := he
  refine ⟨fun a b hab => neg_lt_neg (hl (Fin.rev_lt_rev.2 hab)), fun a => -r (Fin.rev a), fun a => by simp [hr], ?_⟩
  rw [← dualPar_dualPar S, hS]
  ext z
  simp only [dualPar, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨Fin.rev a, by simp⟩
  · rintro ⟨a, rfl⟩
    exact ⟨_, ⟨Fin.rev a, rfl⟩, rfl⟩

theorem card_rev {n : ℕ} (P Q : Fin n → Prop) [DecidablePred P] [DecidablePred Q] (h : ∀ b, P b ↔ Q (Fin.rev b)) :
    (Finset.univ.filter P).card = (Finset.univ.filter Q).card :=
  Finset.card_equiv Fin.revPerm (by simpa using h)

theorem lowK_rev {n : ℕ} (lam : Fin n → ℝ) (ε : Fin n → Bool) (a : Fin n) :
    Formalism.QuantumDeterminants.lowK (fun a => ε (Fin.rev a)) (fun a => -lam (Fin.rev a)) a = -Formalism.QuantumDeterminants.lowK ε lam (Fin.rev a) := by
  simp only [Formalism.QuantumDeterminants.lowK, Pi.add_apply, Pi.sub_apply, Formalism.REAL.rhoN, Formalism.REAL.rhoC]
  rw [card_rev (fun b => a < b ∧ ε (Fin.rev b) ≠ ε (Fin.rev a)) (fun b => b < Fin.rev a ∧ ε b ≠ ε (Fin.rev a))
      (fun b => by simp),
    card_rev (fun b => b < a ∧ ε (Fin.rev b) ≠ ε (Fin.rev a)) (fun b => Fin.rev a < b ∧ ε b ≠ ε (Fin.rev a))
      (fun b => by simp),
    card_rev (fun b => a < b ∧ ε (Fin.rev b) = ε (Fin.rev a)) (fun b => b < Fin.rev a ∧ ε b = ε (Fin.rev a))
      (fun b => by simp),
    card_rev (fun b => b < a ∧ ε (Fin.rev b) = ε (Fin.rev a)) (fun b => Fin.rev a < b ∧ ε b = ε (Fin.rev a))
      (fun b => by simp)]
  ring

theorem revNeg_first {n q : ℕ} {ε : Fin n → Bool} (hq : q ≤ n) (h : ∀ a, ε a = if (a : ℕ) < q then false else true)
    (a : Fin n) (ha : (a : ℕ) < q) : (revNeg ε a : ℕ) = q - 1 - a := by
  have e : negS ε = Finset.univ.map (Fin.castLEEmb hq) := by
    ext a
    simp only [negS, Finset.mem_filter, Finset.mem_univ, true_and, h, Finset.mem_map]
    constructor
    · intro ha
      have ha' : (a : ℕ) < q := by
        by_contra hc
        simp [hc] at ha
      exact ⟨⟨a, ha'⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      simp
  have hc : (negS ε).card = q := by rw [e, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hm : a ∈ negS ε := by simpa [negS, h] using ha
  have hf : ∀ i : Fin (negS ε).card, (((negS ε).orderEmbOfFin rfl i : Fin n) : ℕ) = i := by
    have := Finset.orderEmbOfFin_unique (s := negS ε) (rfl : (negS ε).card = _)
      (f := fun i : Fin (negS ε).card => (⟨i, by have := i.2; omega⟩ : Fin n))
      (fun i => by have := i.2; simp [negS, h]; omega) (fun i j hij => hij)
    intro i
    rw [← this]
  have h1 : revNeg ε a = (revOn ε ⟨a, hm⟩ : Fin n) := Equiv.Perm.ofSubtype_apply_of_mem _ hm
  set i := ((negS ε).orderIsoOfFin rfl).symm ⟨a, hm⟩ with hi
  have h2 : (a : ℕ) = i := by
    rw [← hf i]
    have : ((negS ε).orderIsoOfFin rfl i : Fin n) = a := by rw [hi, OrderIso.apply_symm_apply]
    rw [← this]; rfl
  have h3 : ((revOn ε ⟨a, hm⟩ : Fin n) : ℕ) = (Fin.rev i : ℕ) := hf (Fin.rev i)
  rw [h1, h3, Fin.val_rev]
  have := i.2
  omega

def flipFun {n : ℕ} (q : ℕ) (c : Fin n) : Fin n :=
  if (c : ℕ) < q then c else ⟨n - 1 - (c - q), by have := c.2; omega⟩

theorem flipFun_val {n : ℕ} (q : ℕ) (c : Fin n) :
    (flipFun q c : ℕ) = if (c : ℕ) < q then (c : ℕ) else n - 1 - (c - q) := by
  unfold flipFun
  split_ifs <;> rfl

theorem flipFun_invol {n : ℕ} (q : ℕ) : Function.Involutive (flipFun (n := n) q) := fun c => by
  apply Fin.ext
  have := c.2
  rw [flipFun_val, flipFun_val]
  split_ifs <;> omega

def flipPerm {n : ℕ} (q : ℕ) : Equiv.Perm (Fin n) := (flipFun_invol q).toPerm

theorem flipPerm_val {n : ℕ} (q : ℕ) (c : Fin n) :
    (flipPerm q c : ℕ) = if (c : ℕ) < q then (c : ℕ) else n - 1 - (c - q) := flipFun_val q c

theorem shape {R : Ranks} (h : HCParam R) {p q n : ℕ} (hpq : p + q = R.r) {lam : Fin n → ℝ} {ε : Fin n → Bool}
    (he : IsEnum (dualPar (Formalism.L2.NTheta.holPar p q (Formalism.L2.NTheta.kapW h p q))) lam ε) :
    (∀ a, ε a = if (a : ℕ) < q then false else true) ∧
      ∀ c, Formalism.QuantumDeterminants.lowK ε lam (revNeg ε (flipPerm q c)) = -(wtCol h p q c : ℝ) := by
  have hok := Formalism.L2.NTheta.holOK_kapW h p q hpq
  obtain ⟨rfl, h1⟩ := GlobalTheory.HolDS.enum_holPar hok (isEnum_dual he)
  obtain ⟨_, h2⟩ := GlobalTheory.HolDS.lowK_holPar hok (isEnum_dual he)
  simp only [Fin.cast_eq_self, lowK_rev] at h1 h2
  have hε : ∀ a, ε a = if (a : ℕ) < q then false else true := by
    intro a
    obtain ⟨x, hx⟩ := finSumFinEquiv.surjective (Fin.rev a)
    have h3 := (h1 x).2
    rw [hx, Fin.rev_rev] at h3
    have h4 := congrArg Fin.val hx
    have := a.2
    rcases x with i | i
    · have := i.2
      simp at h4
      rw [h3, if_neg (by omega)]; rfl
    · have := i.2
      simp at h4
      rw [h3, if_pos (by omega)]; rfl
  refine ⟨hε, fun c => ?_⟩
  have hc := c.2
  have hv := flipPerm_val q c
  by_cases hcq : (c : ℕ) < q
  · rw [if_pos hcq] at hv
    have h5 := revNeg_first (by omega) hε (flipPerm q c) (by omega)
    have h6 : revNeg ε (flipPerm q c) = Fin.rev (finSumFinEquiv (Sum.inr ⟨c, hcq⟩)) := by
      apply Fin.ext
      simp
      omega
    rw [h6, ← neg_eq_iff_eq_neg, h2]
    simp [wtCol, Formalism.L2.NTheta.kapW, Formalism.L2.NTheta.kapQ, hcq]
  · rw [if_neg hcq] at hv
    have h5 := revNeg_of_pos ε (a := flipPerm q c) (by rw [hε, if_neg (by omega)])
    have h6 : revNeg ε (flipPerm q c) = Fin.rev (finSumFinEquiv (Sum.inl ⟨c - q, by omega⟩)) := by
      rw [h5]
      apply Fin.ext
      simp
      omega
    rw [h6, ← neg_eq_iff_eq_neg, h2]
    simp [wtCol, Formalism.L2.NTheta.kapW, Formalism.L2.NTheta.kapQ, hcq]

variable {D : D7} (θ : InfFam D) (V : HSp D)

theorem Rder_neg (ρ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) :
    Rder θ V ρ (-X) φ = -Rder θ V ρ X φ := by
  funext g
  have := deriv_comp_neg (fun t : ℝ => φ (g * oneP θ V ρ X t)) 0
  simpa only [Rder, oneP, smul_neg, neg_smul, neg_zero, Pi.neg_apply] using this

theorem Rder_conj (ρ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) (g : GA D V) :
    Rder θ V ρ X (fun g => starRingEnd ℂ (φ g)) g = starRingEnd ℂ (Rder θ V ρ X φ g) :=
  deriv.star

theorem RderC_neg (ρ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) :
    RderC θ V ρ (-Z) φ = -RderC θ V ρ Z φ := by
  have h : conjAt V ρ (-Z) = -conjAt V ρ Z := by simp [conjAt]
  unfold RderC
  rw [h, ← neg_add, neg_sub_neg, ← neg_sub Z, smul_neg, smul_neg, Rder_neg, Rder_neg, smul_neg, neg_add]

theorem RderC_conj (ρ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hZ : conjAt V ρ (conjAt V ρ Z) = Z)
    (φ : GA D V → ℂ) (g : GA D V) :
    RderC θ V ρ Z (fun g => starRingEnd ℂ (φ g)) g = starRingEnd ℂ (RderC θ V ρ (conjAt V ρ Z) φ g) := by
  unfold RderC
  rw [hZ, add_comm (conjAt V ρ Z), ← neg_sub Z, smul_neg, Rder_neg]
  simp [Rder_conj]

theorem Jm_mul_self {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp

theorem Jm_herm {n : ℕ} (ε : Fin n → Bool) : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [diagonal_conjTranspose]
  congr 1
  funext a
  rw [Pi.star_apply]
  split_ifs <;> simp

variable {V} {S : D.what₂.Tau → SPar} (M : DSModel V S)

theorem conjAt_frame (ρ : D.what₂.Tau) (W : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    conjAt V ρ ((M.fr ρ)⁻¹ * W * M.fr ρ) =
      (M.fr ρ)⁻¹ * (-(Formalism.REAL.Jm (M.ε ρ) * Wᴴ * Formalism.REAL.Jm (M.ε ρ))) * M.fr ρ := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit ρ)
  have h1 : M.fr ρ * (M.fr ρ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have h3 : (M.fr ρ)⁻¹ᴴ * (M.fr ρ)ᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  have h4 : ∀ Y : Matrix (Fin V.rank) (Fin V.rank) ℂ, (M.fr ρ)⁻¹ᴴ * ((M.fr ρ)ᴴ * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, h3, Matrix.one_mul]
  unfold conjAt
  rw [← M.fr_gram ρ, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.inv_eq_left_inv (Jm_mul_self (M.ε ρ)),
    ← conjTranspose_nonsing_inv]
  simp only [conjTranspose_mul, Matrix.mul_assoc, h4, Matrix.mul_neg, Matrix.neg_mul]

theorem conj_killed (ρ : D.what₂.Tau) (a b : Fin V.rank) (φ : GA D V → ℂ)
    (h : RderC θ V ρ ((M.fr ρ)⁻¹ * Matrix.single b a 1 * M.fr ρ) φ = 0) :
    RderC θ V ρ ((M.fr ρ)⁻¹ * Matrix.single a b 1 * M.fr ρ) (fun g => starRingEnd ℂ (φ g)) = 0 := by
  funext g
  rw [RderC_conj, conjAt_frame]
  · have h1 : Formalism.REAL.Jm (M.ε ρ) * (Matrix.single a b (1 : ℂ))ᴴ * Formalism.REAL.Jm (M.ε ρ) = Matrix.single b a 1 ∨
        Formalism.REAL.Jm (M.ε ρ) * (Matrix.single a b (1 : ℂ))ᴴ * Formalism.REAL.Jm (M.ε ρ) = -Matrix.single b a 1 := by
      unfold Formalism.REAL.Jm
      by_cases hab : M.ε ρ a = M.ε ρ b
      · left
        ext i j
        simp only [mul_diagonal, diagonal_mul, conjTranspose_apply, Matrix.single_apply]
        by_cases hij : a = j ∧ b = i
        · obtain ⟨rfl, rfl⟩ := hij
          rw [hab]
          split_ifs <;> simp_all
        · rw [if_neg hij, if_neg (fun h' : b = i ∧ a = j => hij h'.symm)]
          simp
      · right
        ext i j
        simp only [mul_diagonal, diagonal_mul, conjTranspose_apply, Matrix.single_apply, Matrix.neg_apply]
        by_cases hij : a = j ∧ b = i
        · obtain ⟨rfl, rfl⟩ := hij
          split_ifs <;> simp_all
        · rw [if_neg hij, if_neg (fun h' : b = i ∧ a = j => hij h'.symm)]
          simp
    rcases h1 with h1 | h1
    · rw [h1, Matrix.mul_neg, Matrix.neg_mul, RderC_neg, h]
      simp
    · rw [h1, neg_neg, h]
      simp
  · rw [conjAt_frame, conjAt_frame]
    congr 2
    simp only [conjTranspose_neg, conjTranspose_mul, Jm_herm, conjTranspose_conjTranspose, Matrix.mul_neg,
      Matrix.neg_mul, neg_neg, ← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]
    rw [Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]

theorem perm_conj {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A) (e : Equiv.Perm (Fin n))
    (W : Matrix (Fin n) (Fin n) ℂ) :
    A⁻¹.submatrix id e * W.submatrix e e * (A⁻¹.submatrix id e)⁻¹ = A⁻¹ * W * A := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hA
  have h1 : (A⁻¹.submatrix id e)⁻¹ = A.submatrix e id := by
    apply Matrix.inv_eq_right_inv
    rw [submatrix_mul_equiv, Matrix.nonsing_inv_mul _ hd, submatrix_id_id]
  rw [h1, submatrix_mul_equiv, submatrix_mul_equiv, submatrix_id_id]

end GlobalTheory.HolRead.AntiHol

open GlobalTheory.HolRead.AntiHol in

theorem GlobalTheory.HolRead.conj_extVec_isHolFor : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (h : D.what₂.Tau → HCParam D.R) (p q : ℕ), IsInfFam θ → p + q = D.R.r → V.rank = D.R.r → (∀ ρ, S ρ = dualPar (Formalism.L2.NTheta.holPar p q (Formalism.L2.NTheta.kapW (h ρ) p q))) → ∀ v : M.Vec, IsExtVec M v → ∃ x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, NegFirst V q x ∧ ∀ (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsMultMap θ M J χ T → IsHolFor θ V x (fun ρ c => wtCol (h ρ) p q c) (fun g => starRingEnd ℂ (T v g)) := by
  intro D θ V S M h p q hθ hpq hV hS v hv
  have hsh := fun ρ => shape (h ρ) hpq (hS ρ ▸ M.enum ρ)
  refine ⟨fun ρ => (M.fr ρ)⁻¹.submatrix id (flipPerm q), fun ρ => ?_, fun J χ T hT => ⟨?_, fun ρ c d hcd => ?_, fun ρ t g => ?_⟩⟩
  · have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit ρ)
    have h1 : M.fr ρ * (M.fr ρ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
    have h2 : (M.fr ρ)⁻¹ᴴ * gramAt D V ρ * (M.fr ρ)⁻¹ = Formalism.REAL.Jm (M.ε ρ) := by
      rw [← M.fr_gram ρ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, h1, conjTranspose_one,
        Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]
    have h3 : ((M.fr ρ)⁻¹.submatrix id (flipPerm q))ᴴ * gramAt D V ρ * (M.fr ρ)⁻¹.submatrix id (flipPerm q) =
        ((M.fr ρ)⁻¹ᴴ * gramAt D V ρ * (M.fr ρ)⁻¹).submatrix (flipPerm q) (flipPerm q) := rfl
    beta_reduce
    rw [h3, h2, Formalism.REAL.Jm, submatrix_diagonal_equiv]
    congr 1
    funext c
    have := c.2
    have hv := flipPerm_val q c
    simp only [Function.comp, (hsh ρ).1]
    by_cases hc : (c : ℕ) < q
    · rw [if_pos hc] at hv
      simp [hv, hc]
    · rw [if_neg hc] at hv
      have : ¬ (flipPerm q c : ℕ) < q := by omega
      simp [this, hc]
  · intro k τs Xs hX g
    exact Complex.conjCLE.contDiff.comp ((hT.aut v).smooth k τs Xs hX g)
  · have hk := (GlobalTheory.T.extremal_vector_annihilated D θ V S M J χ T hθ hT v hv ρ q false (hsh ρ).1).1 (flipPerm q d) (flipPerm q c) (by
      have := c.2
      have := d.2
      have hc := flipPerm_val q c
      have hd := flipPerm_val q d
      have hcd' : (c : ℕ) < d := hcd
      simp only [KillPair, (hsh ρ).1, Fin.lt_def]
      split_ifs at hc hd <;> split_ifs <;> simp <;> omega)
    have h1 : Matrix.single c d (1 : ℂ) =
        (Matrix.single (flipPerm q c) (flipPerm q d) 1).submatrix (flipPerm q) (flipPerm q) := by
      ext i j
      simp [Matrix.single_apply]
    beta_reduce
    rw [h1, perm_conj _ (M.fr_unit ρ)]
    exact conj_killed θ M ρ _ _ _ hk
  · have hk := (GlobalTheory.T.extremal_vector_annihilated D θ V S M J χ T hθ hT v hv ρ q false (hsh ρ).1).2 (fun a => t ((flipPerm q).symm a)) g
    have h1 : diagonal (fun c => Complex.exp ((t c : ℂ) * Complex.I)) =
        (diagonal fun a => Complex.exp ((t ((flipPerm q).symm a) : ℂ) * Complex.I)).submatrix (flipPerm q) (flipPerm q) := by
      rw [submatrix_diagonal_equiv]
      congr 1
      funext c
      simp
    beta_reduce
    rw [h1, perm_conj _ (M.fr_unit ρ), hk, map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
      ← Equiv.sum_comp (flipPerm q)]
    congr 2
    simp only [extWt, (hsh ρ).2, Equiv.symm_apply_apply, neg_mul, Finset.sum_neg_distrib]
    push_cast
    ring

end
end

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.antiholomorphic_extremal_negative_first : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (h : D.what₂.Tau → HCParam D.R) (p q : ℕ), IsInfFam θ → p + q = D.R.r → V.rank = D.R.r → (∀ ρ, S ρ = dualPar (Formalism.L2.NTheta.holPar p q (Formalism.L2.NTheta.kapW (h ρ) p q))) → ∀ v : M.Vec, IsExtVec M v → ∃ x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, NegFirst V q x ∧ ∀ (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsMultMap θ M J χ T → IsHolFor θ V x (fun ρ c => wtCol (h ρ) p q c) (fun g => starRingEnd ℂ (T v g)) := by
  atlas_forward_decl GlobalTheory.HolRead.conj_extVec_isHolFor
end

section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_embedding_label_iff : ∀ (D : D7) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL], LawsJ T → AlgTie T → ∀ (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau), (GoodEmb T.Q.c (res T σ) ↔ labE σ (lab σ ρ) = tauE D ρ) ∧ lab ((starRingEnd ℂ).comp σ) ρ = lab σ ρ := by
  first | exact @GlobalTheory.HolRead.good_iff_labE_and_lab_conj | exact GlobalTheory.HolRead.good_iff_labE_and_lab_conj | (intros; apply GlobalTheory.HolRead.good_iff_labE_and_lab_conj <;> assumption)
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead

theorem card_le_finrank_of_semilinear {K C Y : Type} [Field K] [AddCommGroup C] [Module K C] [FiniteDimensional K C]
    [AddCommGroup Y] [Module ℂ Y] {σ : K →+* ℂ} (j : C →ₛₗ[σ] Y) {m : ℕ} (f : Fin m → Y) (hf : LinearIndependent ℂ f)
    (hm : ∀ k, f k ∈ Submodule.span ℂ (Set.range j)) : m ≤ Module.finrank K C := by
  let b := Module.finBasis K C
  have hle : Submodule.span ℂ (Set.range j) ≤ Submodule.span ℂ (Set.range fun k => j (b k)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, rfl⟩
    rw [← b.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have h1 := linearIndependent_le_span_aux' f hf (Set.range fun k => j (b k))
    (by rintro _ ⟨k, rfl⟩; exact hle (hm k))
  have h2 : Fintype.card (Set.range fun k => j (b k)) ≤ Module.finrank K C :=
    (Fintype.card_range_le _).trans (Fintype.card_fin _).le
  exact (Fintype.card_fin m).symm.le.trans (h1.trans h2)

theorem linearIndependent_conj {ι : Type} {m : ℕ} {f : Fin m → ι → ℂ} (hf : LinearIndependent ℂ f) :
    LinearIndependent ℂ fun k x => starRingEnd ℂ (f k x) := by
  rw [Fintype.linearIndependent_iff] at hf ⊢
  intro c hc k
  have h := hf (fun k => starRingEnd ℂ (c k)) (funext fun x => by
    have := congrArg (starRingEnd ℂ) (congrFun hc x)
    simpa [Finset.sum_apply, map_sum] using this) k
  simpa using h

theorem eval_eq_zero {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (e : H →ₗ[ℂ] MMap M) (d : ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V))
    (he : ∀ x y, inner ℂ x y = d * ipM M μ 𝓕 (e x) (e y)) (v : M.Vec) (hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1) (x : H)
    (hx : e x v = 0) : x = 0 := by
  rw [← inner_self_eq_zero (𝕜 := ℂ), he]
  refine mul_eq_zero_of_right _ ?_
  by_cases h : ∃ c, IsMultIP M μ 𝓕 (e x) (e x) c
  · have h1 := (ipM_spec M μ 𝓕 _ _ h v v).2
    simp only [hx, Pi.zero_apply, mul_zero, integral_zero, inner_self_eq_norm_sq_to_K, hv] at h1
    simpa using h1.symm
  · exact dif_neg h

set_option maxHeartbeats 1000000 in

theorem adel_mem_span {D : D7} (T : CoreJ D) (h : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ)
    (hσ : GoodEmb T.Q.c σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hD : Dom a n) (hL : LastPos (T.Q.Dw j) a)
    (hn : 8 * D.R.f * D.R.r + 4 ≤ n) (P : FDSec (T.U j σ).X) (hP : IsHolCusp (T.U j σ).X (laU (T.U j σ) a n) P) :
    adel (T.V j σ) (T.dict j σ) (T.mu j σ) P ∈ Submodule.span ℂ
      (Set.range ((adel (T.V j σ) (T.dict j σ) (T.mu j σ)).comp (rdC (T.U j) σ a n))) := by
  obtain ⟨-, hA, -, -, -, hdeg, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  have hr1 : 1 ≤ D.R.r := (hnum j hj).2.1
  obtain ⟨hrk, hW⟩ := h.modelW j hj σ hσ
  obtain ⟨th, hrk', -, hdict⟩ := h.dictU j hj σ hσ
  have hG := GlobalTheory.RunIn.gamAt_of_lawsJ D T h
  have hle := GlobalTheory.Dict.holSub0_le_span_cusp GlobalTheory.chartIndependence_unconditional D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r
    (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hr1 hA (fun σ hσ => h.unf j hj σ hσ) σ hσ
    (fun k k' => ⟨(hW k).1.trans (hW k').1.symm, (hW k).2.trans (hW k').2.symm⟩)
    (by
      intro k ga hga hv
      refine hG j hj σ hσ k ga hga fun x hx => ?_
      obtain ⟨u, hu, he⟩ := hv x hx
      refine ⟨u, hu, ?_⟩
      rw [he, Nat.cast_smul_eq_nsmul]
      exact add_sub_cancel_left _ _)
    a n hD hL
    (by
      rw [hdeg]
      calc 4 * (2 * D.R.f * D.R.r) + 4 = 8 * D.R.f * D.R.r + 4 := by ring
        _ ≤ n := hn)
    (fun k => h.chiTriv j hj σ hσ a n hD k)
  have hle' : GlobalTheory.Dict.holSub0 (T.U j σ).X (laU (T.U j σ) a n) ≤ Submodule.span ℂ (Set.range (rdC (T.U j) σ a n)) := by
    refine le_trans hle (Submodule.span_mono ?_)
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨⟨f, hf⟩, rfl⟩
  have hmem : (fun k => ((T.U j σ).X k).dom.indicator (P k)) ∈ GlobalTheory.Dict.holSub0 (T.U j σ).X (laU (T.U j σ) a n) := by
    refine ⟨Submodule.subset_span fun k => ?_, fun k x hx => Set.indicator_of_notMem hx _⟩
    exact (GlobalTheory.DomCongr.bddSec_cusp_congr _ _ ((T.U j σ).X k) _ (P k) _
      (fun x hx => (Set.indicator_of_mem hx _).symm)).2 (hP k)
  have he : adel (T.V j σ) (T.dict j σ) (T.mu j σ) (fun k => ((T.U j σ).X k).dom.indicator (P k)) =
      adel (T.V j σ) (T.dict j σ) (T.mu j σ) P := by
    funext g
    show T.mu j σ g * ((T.U j σ).X (T.dict j σ g).1).dom.indicator (P (T.dict j σ g).1) (T.dict j σ g).2 =
      T.mu j σ g * P (T.dict j σ g).1 (T.dict j σ g).2
    rw [Set.indicator_of_mem (hdict.2.2.2.1 g)]
  rw [← he]
  have h2 := Submodule.mem_map_of_mem (f := adel (T.V j σ) (T.dict j σ) (T.mu j σ)) (hle' hmem)
  rw [Submodule.map_span, ← Set.range_comp] at h2
  exact h2

set_option maxHeartbeats 1000000 in

theorem card_le_finrank_cusp {D : D7} (T : CoreJ D) (h : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ)
    (hσ : GoodEmb T.Q.c σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hD : Dom a n) (hL : LastPos (T.Q.Dw j) a)
    (hn : 8 * D.R.f * D.R.r + 4 ≤ n) (θ : InfFam D) (hθ : IsInfFam θ) (w : D.what₂.Tau → ℕ → ℤ) (e : D.what₂.Tau → ℤ)
    (hmu : ∀ k ∈ T.Kf j σ, T.mu j σ k = 1) (hinf : ∀ ρ, HasInfExp D (T.chiW j σ) ρ (-(e ρ : ℚ)))
    (hw : ∀ k (ρ : D.what₂.Tau) (τ : ((T.U j σ).X k).Ψ), τ.1 = tauE D ρ → ∀ c : Fin D.R.r,
      laU (T.U j σ) a n k τ c = w ρ c + e ρ)
    {W : HSp D} (hV : T.V j σ = W) (x : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (hx : NegFirst W (D.R.sigW j).2 x) {m : ℕ} (φ : Fin m → GA D W → ℂ) (hφ : LinearIndependent ℂ φ)
    (hh : ∀ k, IsHolFor θ W x (fun ρ c => w ρ c) (φ k)) (hl : ∀ k, ∀ γ ∈ GQ W, ∀ g, φ k (γ * g) = φ k g)
    (hk : ∀ Kf, IsLevelK W (D.host.g 0 * D.host.g 1) Kf → ∀ k, ∀ κ ∈ Kf, ∀ g, φ k (g * κ) = φ k g)
    (hb : ∀ k, ∃ C : ℝ, ∀ g, ‖φ k g‖ ≤ C) : m ≤ Module.finrank T.Q.c.F (T.cuspA j a n) := by
  subst hV
  obtain ⟨hr, x₀, hB⟩ := GlobalTheory.T.base_dictionary_exists_good_embedding D T h j hj σ hσ θ hθ
  have hK := h.levelK j hj σ hσ
  have hM := h.muUnit j hj σ hσ
  have hq : ∀ k, ((T.U j σ).X k).p0 = (D.R.sigW j).2 := fun k =>
    ((h.unf j hj σ hσ).2.1 k).1.trans (h.pins.2.2.2 j hj).2.1
  obtain ⟨u, hu⟩ := GlobalTheory.T.character_expansion_weight_compat D θ _ _ hr _ _ _ _ x₀ (laU (T.U j σ) a n) x _ (fun ρ c => w ρ c) e (T.mu j σ) hθ hB
    (fun k hk => ((hK k).1 hk).1) hq hx hM.1 hM.2.1 hM.2.2.1 hmu
    (GlobalTheory.T.archimedean_character_det_power D θ _ _ _ e hθ (h.muVal j hj σ hσ) hinf) (fun k ρ τ hτ c => hw k ρ τ hτ _)
    (h.chiTriv j hj σ hσ a n hD) (fun k τ c d hc hd => by
      rw [← hq k] at hc hd
      simp only [laU, if_pos hd, if_neg (not_le.2 hc)]
      omega)
  have : FiniteDimensional T.Q.c.F (T.cuspA j a n) := h.cuspFD j hj a n hD
  refine card_le_finrank_of_semilinear ((adel (T.V j σ) (T.dict j σ) (T.mu j σ)).comp (rdC (T.U j) σ a n))
    (fun k g => φ k (g * u)) ?_ fun k => ?_
  · rw [Fintype.linearIndependent_iff] at hφ ⊢
    intro c hc
    refine hφ c (funext fun g => ?_)
    have := congrFun hc (g * u⁻¹)
    simpa [Finset.sum_apply] using this
  · obtain ⟨P, hP, hPe⟩ := hu (φ k) (hh k) (hl k) (hk _ hK k) (hb k)
    rw [show (fun g => φ k (g * u)) = adel (T.V j σ) (T.dict j σ) (T.mu j σ) P from funext hPe]
    exact adel_mem_span T h j hj σ hσ a n hD hL hn P hP

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

def evL (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (v : (R.MW i σ).Vec) : (R.HW i σ).H →ₗ[ℂ] (GA D (Wc D i) → ℂ) where
  toFun := evAt R i σ v
  map_add' x y := by simp [evAt]
  map_smul' c x := by simp [evAt]

theorem parAt_sig (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) :
    Formalism.L2.NTheta.holPar _ _ (kapAt (Wc D i) σ ρ) = Formalism.L2.NTheta.holPar (D.R.sigW ((i : ℕ) + 1)).1 (D.R.sigW ((i : ℕ) + 1)).2
      (Formalism.L2.NTheta.kapW (D.hc (lab σ ρ)) _ _) := by
  unfold kapAt
  rw [show (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ (inR i).1 (inR i).2 _]

set_option maxHeartbeats 1000000 in

theorem finrank_model_le (hP : GlobalTheory.Published.CuspRapidDecay) (hn : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) (hL : R.toLevCh.Is A.μ0)
    (hθ : R.models_inf) (hH : R.models_HW) (h : TieIn T R κ v₀) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) :
    Module.finrank ℂ (R.HW i σ).H ≤ Module.finrank T.Q.c.F (Cu T κ i) := by
  have hpq : (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 = D.R.r := by
    have := D.R.m_add_three_le_k
    have := i.2
    simp only [Ranks.sigW, Ranks.r]
    omega
  obtain ⟨ρ₀⟩ : Nonempty D.what₂.Tau := by
    obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    by_cases h1 : ∃ ρ, tauE D ρ = τ
    · exact ⟨h1.choose⟩
    · exact ⟨(not_not.1 (mt (GlobalTheory.SmoothForms.RealPts.tauE_cm D τ).2 h1)).choose⟩
  have hn' : 8 * D.R.f * D.R.r + 4 ≤ (κ i).n := (h.kap i ρ₀).2.2 ▸ hn
  let β := Module.finBasis ℂ (R.HW i σ).H
  have hM : ∀ x, IsMultMap R.θ (R.MW i σ) (levS _ (R.βW i) (R.datWp i R.triv)) (Lev.levChi _ (R.βW i) (R.datWp i R.triv))
      ((R.HW i σ).e x) := fun x =>
    (GlobalTheory.MultMem.mem_mult_iff D _ _ _ _ _ _ _).1 ((hH i σ).2.1.le ⟨x, rfl⟩)
  have hind : LinearIndependent ℂ fun k => (R.HW i σ).e (β k) (v₀ i σ) :=
    β.linearIndependent.map' (evL T R i σ (v₀ i σ)) (LinearMap.ker_eq_bot'.2 fun x hx =>
      eval_eq_zero _ (R.HW i σ).e _ _ _ (hH i σ).2.2 _ ((h.hv₀ i σ).norm R) x hx)
  have hlev : ∀ Kf, IsLevelK (Wc D i) (D.host.g 0 * D.host.g 1) Kf → ∀ k, ∀ c ∈ Kf, ∀ g,
      (R.HW i σ).e (β k) (v₀ i σ) (g * c) = (R.HW i σ).e (β k) (v₀ i σ) g := fun Kf hK k c hc g => by
    obtain ⟨h1, h2⟩ := GlobalTheory.T.level_character_trivial_on_subgroup D T0 R.toLevCh A.μ0 hL i Kf hK c hc
    rw [(hM _).lev _ c h1, h2, one_mul]
  have hbd : ∀ k, ∃ C : ℝ, ∀ g, ‖(R.HW i σ).e (β k) (v₀ i σ) g‖ ≤ C := fun k =>
    GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ ((hM _).aut _) ((hM _).cusp _)
  have key : ∀ σ' : D.what₂.LL →+* ℂ, GoodEmb T.Q.c (res T σ') → (∀ ρ, lab σ' ρ = lab σ ρ) →
      ∀ x, NegFirst (Wc D i) (D.R.sigW ((i : ℕ) + 1)).2 x → ∀ φ : Fin (Module.finrank ℂ (R.HW i σ).H) → GA D (Wc D i) → ℂ,
      LinearIndependent ℂ φ → (∀ k, IsHolFor R.θ (Wc D i) x
        (fun ρ c => wtCol (D.hc (lab σ ρ)) (D.R.sigW ((i : ℕ) + 1)).1 (D.R.sigW ((i : ℕ) + 1)).2 c) (φ k)) →
      (∀ k, ∀ γ ∈ GQ (Wc D i), ∀ g, φ k (γ * g) = φ k g) →
      (∀ Kf, IsLevelK (Wc D i) (D.host.g 0 * D.host.g 1) Kf → ∀ k, ∀ c ∈ Kf, ∀ g, φ k (g * c) = φ k g) →
      (∀ k, ∃ C : ℝ, ∀ g, ‖φ k g‖ ≤ C) → Module.finrank ℂ (R.HW i σ).H ≤ Module.finrank T.Q.c.F (Cu T κ i) := by
    intro σ' hσ' hlab x hx φ h1 h2 h3 h4 h5
    choose e he using fun ρ => (D.hc (lab σ' ρ)).e_int i
    refine card_le_finrank_cusp T h.laws _ (inR i) _ hσ' _ _ (dom_wtA (κ i)) (GlobalTheory.T.last_weight_positive D T κ h.laws h.kap i) hn' R.θ hθ
      (fun ρ c => wtCol (D.hc (lab σ ρ)) (D.R.sigW ((i : ℕ) + 1)).1 (D.R.sigW ((i : ℕ) + 1)).2 c) e
      (GlobalTheory.T.level_character_trivial_on_level D G Pl0 T0 A T R h.laws hL h.chiR i σ' hσ') (fun ρ => he ρ ▸ (h.chiR i σ' hσ').2.2.1 ρ)
      (fun k ρ τ hτ c => ?_) (h.laws.spaceW _ (inR i) _ hσ') x hx φ h1 h2 h3 h4 h5
    rw [← hlab ρ]
    exact GlobalTheory.T.weight_label_at_unfolding D T κ h.laws h.alg h.kap i σ' hσ' e (fun ρ => (he ρ).symm) k ρ τ hτ c
  by_cases hσ : GoodEmb T.Q.c (res T σ)
  · obtain ⟨x, hx, hhol⟩ := GlobalTheory.T.holomorphic_extremal_negative_first D R.θ _ _ (R.MW i σ) (fun ρ => D.hc (lab σ ρ)) _ _ hθ hpq (rank_Wc i)
      (fun ρ => (if_pos ((GlobalTheory.T.good_embedding_label_iff D T h.laws h.alg σ ρ).1.1 hσ)).trans (parAt_sig i σ ρ)) _ (h.hv₀ i σ).1
    exact key σ hσ (fun _ => rfl) x hx _ hind (fun k => hhol _ _ _ (hM _)) (fun k => ((hM _).aut _).left) hlev hbd
  · obtain ⟨x, hx, hhol⟩ := GlobalTheory.T.antiholomorphic_extremal_negative_first D R.θ _ _ (R.MW i σ) (fun ρ => D.hc (lab σ ρ)) _ _ hθ hpq (rank_Wc i)
      (fun ρ => (if_neg (mt (GlobalTheory.T.good_embedding_label_iff D T h.laws h.alg σ ρ).1.2 hσ)).trans (congrArg dualPar (parAt_sig i σ ρ))) _
      (h.hv₀ i σ).1
    refine key ((starRingEnd ℂ).comp σ) (good_resC T hσ) (fun ρ => (GlobalTheory.T.good_embedding_label_iff D T h.laws h.alg σ ρ).2) x hx _
      (linearIndependent_conj hind) (fun k => hhol _ _ _ (hM _)) (fun k γ hγ g => ?_) (fun Kf hK k c hc g => ?_)
      fun k => (hbd k).imp fun C hC g => ?_
    · exact congrArg _ (((hM _).aut _).left γ hγ g)
    · exact congrArg _ (hlev Kf hK k c hc g)
    · exact (Complex.norm_conj _).trans_le (hC g)

end GlobalTheory.HolRead
end
end
