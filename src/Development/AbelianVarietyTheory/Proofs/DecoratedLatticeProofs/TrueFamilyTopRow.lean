import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FamCol
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PureTensorOZeroEqJetP
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.GoodLatCM
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharOfTrace
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AmbIsTrueOfAmbTrue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiTContinuous
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnStepsAreStandardHermitianPairsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCharExponentInfinityKernelShift
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTupleChainAdelicData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnsBranchingMapEquivariantNonzeroCommon
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastGroupEmbeddingRealComponentsBlockForm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelPartLawsOfColumnPins
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLastPeriodClassDataOfLastStep
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopLevExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoefficientVectorReadingRealRepresentation
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SurjectiveTopMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleChainComplexFormsEqAlgebraicModularForms

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk
open scoped TensorProduct Classical
namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem xi_zero_embedding_value (D : D7) (hc : D.host.ccK = ⊤) (τ : D.what₂.Tau) :
    tauE D τ D.host.xi0 = Complex.I * ((Real.sqrt D.host.d)⁻¹ : ℝ) := by
  have h1 : tauE D τ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℝ) :=
    ((Formalism.BasicNotions.factEmb D.R D.host).2 _).2 (D.eTau τ).2
  have hd : 0 < Real.sqrt D.host.d := Real.sqrt_pos.2 (Nat.cast_pos.2 D.host.hyp.2.1.pos)
  rw [Host.xi0, hc, Ideal.absNorm_top, map_div₀, map_mul, h1, map_natCast, map_neg, map_one]
  have : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd.ne'
  push_cast
  field_simp
  simp

theorem stdPair_world {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ) (θ : InfFam (I.rec7 l Z)) (hψ : IsStdChar (I.rec7 l Z) ψ (-1)) (hθ : IsInfFam θ)
    (i : ℕ) : StdPair θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) I.A.δ I.A.sc ψ := by
  obtain ⟨hs, hX, -⟩ := hI.spaces
  have hg : ∀ j, ((I.rec7 l Z).sp.X j).gram = 1 := fun j => by
    have e : (I.rec7 l Z).sp.X j = Formalism.BasicNotions.Examples₂.posSpace hs (B.R.N j) := hX j
    rw [e]
    refine Matrix.ext fun a b => ?_
    refine (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs (B.R.N j) (fun _ => false) (B.R.N j) 0 a b).trans ?_
    by_cases h : a = b
    · subst h
      rw [Matrix.one_apply_eq]
      exact (if_pos rfl).trans (by simp [Formalism.BasicNotions.Examples₂.sgn]; rfl)
    · rw [Matrix.one_apply_ne h]
      exact if_neg h
  have hr : ∀ j, ((I.rec7 l Z).sp.X j).rank = B.R.N j := fun j => by
    have e : (I.rec7 l Z).sp.X j = Formalism.BasicNotions.Examples₂.posSpace hs (B.R.N j) := hX j
    rw [e]; rfl
  have hev : ∀ j, Even (B.R.N j) := fun j =>
    B.R.k_even.add (Even.mul_left (B.R.t_odd.add_one) j)
  have hδ : I.J.δ ≠ 0 := I.J.δ_ne_zero
  have hd : 0 < Real.sqrt B.host.d := Real.sqrt_pos.2 (Nat.cast_pos.2 B.host.hyp.2.1.pos)
  refine ⟨hψ, hθ, hg _, hg _, (I.rec7 l Z).sp.X_sig _, (I.rec7 l Z).sp.X_sig _, ?_, B.ccK_top, hδ,
    xi_zero_embedding_value _ B.ccK_top, ?_⟩
  · rw [hr, hr]
    refine ⟨?_, ?_, hev _, hev _⟩
    · have := B.R.m_add_three_le_k; unfold Ranks.N; omega
    · unfold Ranks.N; nlinarith
  · have hA := Formalism.MainNotions.Ext.area_lamOf (I.rec7 l Z) ⊤ top_ne_bot I.J.δ hδ
    rw [Formalism.MainNotions.Ext.discr_K (I.rec7 l Z).host, Ideal.absNorm_top] at hA
    have hA' : Formalism.MainNotions.TaylorLogMetric.area (Th.lamOf B.host ⊤ I.J.δ) = ‖I.J.δ‖ ^ 2 * Real.sqrt B.host.d / 2 := by
      refine hA.trans ?_
      simp
      exact Or.inl rfl
    show (Formalism.MainNotions.TaylorLogMetric.area (Th.lamOf B.host ⊤ I.J.δ))⁻¹ * ‖I.J.δ‖ ^ 2 = 2 * (Real.sqrt B.host.d)⁻¹
    rw [hA']
    have : ‖I.J.δ‖ ≠ 0 := norm_ne_zero_iff.2 hδ
    field_simp

end GlobalTheory.AdForm
end
end

section
section
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.JetScales

theorem exists_jetS : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X →
    ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ →
      ∃ s, JetS I l Z ψ θ s := by
  intro B X I hI hP l Z ψ θ hψ hθ
  have hstep : ∀ j (hj : j + 1 ≤ B.R.m), ∃ s : ℂ, s ≠ 0 ∧ ∀ f, IsHol θ ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) ψ f → ∀ P,
      pureTensorO ψ θ _ _ (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P 0 =
        jetP _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj)) (rankN (I.rec7 l Z) (j + 1) hj) s (ColDat.xiS θ j hj f) P :=
    fun j hj => GlobalTheory.AdForm.JetRead.pureTensorO_zero_eq_jetP (I.rec7 l Z) ψ θ _ _ _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj))
      (rankN (I.rec7 l Z) (j + 1) hj) I.A.δ I.A.sc (stdPair_world I hI l Z ψ θ hψ hθ j)
  refine ⟨fun j => if hj : j + 1 ≤ B.R.m then (hstep j hj).choose else 1, fun j hj => ?_⟩
  simp only [dif_pos hj]
  exact (hstep j hj).choose_spec

end GlobalTheory.AdForm.JetScales
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_jetScale_trueColumns : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∃ s, JetS I l Z ψ θ s := by
  atlas_forward_decl GlobalTheory.AdForm.JetScales.exists_jetS
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm

theorem isTr_unique {ι : Type} [Fintype ι] {n : ℕ} {G : ι → Matrix (Fin n) (Fin n) ℂ} {g : ι → Matrix (Fin n) (Fin n) ℂ}
    {y₁ y₂ y' : Frames G} (h₁ : IsTr g y₁ y') (h₂ : IsTr g y₂ y') : y₁.1 = y₂.1 := by
  funext τ
  have hu : IsUnit (g τ).det := by
    have h := y'.2 τ
    rw [h₁ τ, Matrix.det_mul] at h
    exact isUnit_of_mul_isUnit_left h
  have e : g τ * y₁.1 τ = g τ * y₂.1 τ := by rw [← h₁ τ, ← h₂ τ]
  calc y₁.1 τ = (g τ)⁻¹ * (g τ * y₁.1 τ) := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
    _ = (g τ)⁻¹ * (g τ * y₂.1 τ) := by rw [e]
    _ = y₂.1 τ := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]

theorem jOf_exists : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks), IsInfFam R.θ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), ∃ J, JOf R j J := by
  intro B X I _ _ l Z G _ _ Pl0 T F Ks _ _ _ R _ j
  refine ⟨fun v k z' => if h : ∃ z : FrN (I.rec7 l Z) (B.R.N B.R.m - 1),
      IsTr (infM R.θ _ (rankP (I.rec7 l Z)) k) z z' then j v ⟨h.choose.1, h.choose.2⟩ else 0, ?_⟩
  intro v k _ z z' hz
  have h : ∃ z : FrN (I.rec7 l Z) (B.R.N B.R.m - 1), IsTr (infM R.θ _ (rankP (I.rec7 l Z)) k) z z' := ⟨z, hz⟩
  simp only [dif_pos h]
  have e := isTr_unique h.choose_spec hz
  exact congrArg (j v) (Subtype.ext e)

end GlobalTheory.AdForm
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_translates_of_values_frames : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks), IsInfFam R.θ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), ∃ J, JOf R j J := by
  atlas_forward_decl GlobalTheory.AdForm.jOf_exists
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumns_branchingMap_equivariant_nonzero_common : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (hN : B.R.N B.R.m = (B.R.N B.R.m - 1) + 1), (∀ τ, Formalism.L2.Col.Br.Interlace hN (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u B.R.m τ) (sgT (D := (I.rec7 l Z)) u τ)) ∧ BrEqv hN _ _ (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u B.R.m) (sgT (D := (I.rec7 l Z)) u) (lowOf I l Z u) ∧ (∃ Φ ∈ ValC _ (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u B.R.m), lowOf I l Z u Φ ≠ 0) ∧ ∀ (a : I.ι) z c (y : FrN (I.rec7 l Z) (B.R.N B.R.m - 1)), (I.per l u a).lowerMap z c ⟨y.1, y.2⟩ = lowOf I l Z u (fun y' => z c ⟨y'.1, y'.2⟩) y := by
  first | exact @GlobalTheory.TrueBranch.branching_true_columns | exact GlobalTheory.TrueBranch.branching_true_columns | (intros; apply GlobalTheory.TrueBranch.branching_true_columns <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastGroup_embedding_real_components_block_form : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (θ : InfFam (I.rec7 l Z)), IsInfFam θ → ∀ (emb : GA (I.rec7 l Z) (I.rec7 l Z).sp.X' →* GA (I.rec7 l Z) ((I.rec7 l Z).sp.X B.R.m)) (hN : B.R.N B.R.m = (B.R.N B.R.m - 1) + 1), IsEmbTop (D := I.rec7 l Z) (TC.z0 X u) emb → ∀ (k : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') (τ : (I.rec7 l Z).what₂.Tau), GlobalTheory.BranchFormula.IsBlock hN (infM θ _ (rankN (I.rec7 l Z) B.R.m le_rfl) (emb k) τ) (infM θ _ (rankP (I.rec7 l Z)) k τ) 1 := by
  first | exact @GlobalTheory.EmbTopBlock.isBlock_infM_emb | exact GlobalTheory.EmbTopBlock.isBlock_infM_emb | (intros; apply GlobalTheory.EmbTopBlock.isBlock_infM_emb <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000

namespace GlobalTheory.RealTrue

theorem ontoUni_reindex {ι K : Type} [Group K] [TopologicalSpace K] {a b : ℕ} (h : a = b)
    {r : K → ι → Matrix (Fin a) (Fin a) ℂ} (hr : OntoUni r) :
    OntoUni fun k τ => (r k τ).reindex (finCongr h) (finCongr h) := by
  subst h; simpa using hr

theorem ontoUni_one {ι K : Type} [Group K] [TopologicalSpace K] {a : ℕ}
    {r : K → ι → Matrix (Fin a) (Fin a) ℂ} (hr : OntoUni r) (τ : ι) : r 1 τ = 1 := by
  have hm := hr.mul 1 1 τ
  rw [mul_one] at hm
  have hu := Matrix.mem_unitaryGroup_iff'.1 (hr.uni 1 τ)
  calc r 1 τ = (star (r 1 τ) * r 1 τ) * r 1 τ := by rw [hu, Matrix.one_mul]
    _ = star (r 1 τ) * (r 1 τ * r 1 τ) := Matrix.mul_assoc _ _ _
    _ = 1 := by rw [← hm, hu]

theorem inN_one {D : D7} (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) (τ : D.what₂.Tau) :
    inN θ V (fun _ => 1) hn g τ = infM θ V hn g τ := by
  simp [inN, GlobalTheory.SeeSaw.inB, infM]

theorem valC_transport {ι : Type} [Fintype ι] {n : ℕ} {G G' : ι → Matrix (Fin n) (Fin n) ℂ} (h : G = G')
    (lam : ι → DomWeight n) (f : Formalism.L2.Forms.Frames G → ℂ) (hf : f ∈ ValC G lam) :
    (fun z : Formalism.L2.Forms.Frames G' => f ⟨z.1, z.2⟩) ∈ ValC G' lam := by
  subst h; exact hf

end GlobalTheory.RealTrue

open GlobalTheory.RealTrue in

theorem GlobalTheory.AdForm.realOf_is : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → IsEmbTop (D := (I.rec7 l Z)) (TC.z0 X u) ((g.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _)) → (realOf u R g s J).Is := by
  intro B X I hOk hPins l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ s J hX j hJ hJO hEmb
  have hstd := GlobalTheory.T.trueColumnSteps_are_standardHermitianPairs I hOk hPins l Z R.ψ R.θ hX.std hX.inf
  have hm2 : 2 ≤ B.R.m := B.R.two_le_m
  have hgX : ∀ i, i ≤ B.R.m → ((I.rec7 l Z).sp.X i).gram = 1 := by
    intro i hi
    rcases Nat.lt_or_ge i B.R.m with h | h
    · exact (hstd.1 i h).gS
    · obtain rfl : i = B.R.m := le_antisymm hi h
      have := (hstd.1 (B.R.m - 1) (by omega)).gT
      rwa [show B.R.m - 1 + 1 = B.R.m by omega] at this
  have hrk : ∀ i, i < B.R.m → 0 < B.R.N i ∧ B.R.N i ≤ B.R.N (i + 1) := by
    intro i hi
    have h := (hstd.1 i hi).rk
    rw [rankN (I.rec7 l Z) i hi.le, rankN (I.rec7 l Z) (i + 1) hi] at h
    exact ⟨h.1, h.2.1.le⟩
  have huni : ∀ i (hi : i ≤ B.R.m), OntoUni fun k : GinfC ((I.rec7 l Z).sp.X i) => (realOf u R g s J).r i hi k.1 := by
    intro i hi
    have hB := (hX.xs i hi).2.1
    have := GlobalTheory.SeeSaw.ontoUni_inB (I.rec7 l Z) R.θ ((I.rec7 l Z).sp.X i) (g.x i).B hX.inf (fun τ => by
      rw [hB]; simp [gramAt, hgX i hi])
    exact ontoUni_reindex (rankN (I.rec7 l Z) i hi) this
  have huniT : OntoUni fun k : GinfC (I.rec7 l Z).sp.X' => (realOf u R g s J).rT k.1 := by
    have := GlobalTheory.SeeSaw.ontoUni_inB (I.rec7 l Z) R.θ (I.rec7 l Z).sp.X' (fun _ => 1) hX.inf (fun τ => by
      simp [gramAt, hstd.2.1])
    exact ontoUni_reindex (rankP (I.rec7 l Z)) this
  have hrT : ∀ k, (realOf u R g s J).rT k = infM R.θ _ (rankP (I.rec7 l Z)) k := fun k => funext fun τ => inN_one _ _ _ _ _
  have hone : ∀ τ, infM R.θ _ (rankP (I.rec7 l Z)) 1 τ = 1 := by
    intro τ
    have := ontoUni_one huniT τ
    rw [← hrT]; exact this
  have htr1 : ∀ z : FrN (I.rec7 l Z) (B.R.N B.R.m - 1), IsTr (infM R.θ _ (rankP (I.rec7 l Z)) 1) z z := by
    intro z τ; rw [hone, Matrix.one_mul]
  have hJ1 : ∀ v, J v 1 = fun z => j v ⟨z.1, z.2⟩ := fun v => funext fun z => hJO v 1 (Subgroup.one_mem _) z z (htr1 z)
  have hG : gramC (gramP (I.rec7 l Z)) (Formalism.L2.Forms.embT (I.rec7 l Z)) = fun _ => 1 := by
    funext τ; simp [gramC, gramP, hstd.2.1]
  refine ⟨huni, ?_, hrk, ?_, ?_, ?_, ?_⟩
  · exact huniT
  · intro i τ
    simp only [realOf]
    split_ifs with h
    · exact one_ne_zero
    · exact div_ne_zero h (hstd.2.2.2.1 τ)
  · intro i hi τ
    obtain ⟨Ch, _, A, hA, -⟩ := GlobalTheory.T.exists_tupleChain_adelicData I hOk hPins l Z u I.mu0
    obtain ⟨e, -, he⟩ := GlobalTheory.T.exists_charExponent_infinity_kernel_shift I hOk hPins l Z u I.mu0 Ch A hA i hi
    exact Int.toNat_of_nonneg (he τ).2.2
  · intro v
    refine ⟨?_, fun k hk z z' hz => ?_⟩
    · show J v 1 ∈ ValC _ (sgT (D := I.rec7 l Z) u)
      rw [hJ1 v]
      have hm : j v ∈ ValC (gramC (gramP (I.rec7 l Z)) (Formalism.L2.Forms.embT (I.rec7 l Z))) (sgT (D := I.rec7 l Z) u) := by
        rw [← hJ.range]; exact LinearMap.mem_range_self j v
      exact valC_transport hG _ _ hm
    · rw [hrT] at hz
      show J v k z' = J v 1 z
      rw [hJO v k hk z z' hz, hJO v 1 (Subgroup.one_mem _) z z (htr1 z)]
  · intro n hn
    subst hn
    have hN : B.R.N B.R.m = (B.R.N B.R.m - 1) + 1 := by
      have := hrk (B.R.m - 1) (by omega)
      rw [show B.R.m - 1 + 1 = B.R.m by omega] at this
      omega
    obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.T.trueColumns_branchingMap_equivariant_nonzero_common I hOk hPins l Z u hN
    refine ⟨hN, h1, h2, h3, ?_⟩
    intro k hk τ
    have hb := GlobalTheory.T.lastGroup_embedding_real_components_block_form I hOk hPins l Z u R.θ hX.inf _ hN hEmb k τ
    have hB := (hX.xs B.R.m le_rfl).2.1
    show GlobalTheory.BranchFormula.IsBlock hN (inN R.θ _ (g.x B.R.m).B (rankN (I.rec7 l Z) B.R.m le_rfl) ((g.oT B.R.m rfl).emb (k, 1)) τ) (inN R.θ _ (fun _ => 1) (rankP (I.rec7 l Z)) k τ) 1
    rw [hB]
    first
      | simpa only [inN_one] using hb
      | simpa [inN, GlobalTheory.SeeSaw.inB, infM] using hb
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumns_realData_spec : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → IsEmbTop (D := (I.rec7 l Z)) (TC.z0 X u) ((g.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _)) → (realOf u R g s J).Is := by
  atlas_forward_decl GlobalTheory.AdForm.realOf_is
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.PerIn

theorem exists_Mt_of_rep_values : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Formalism.BasicNotions.Ranks} {I : GlobalTheory.Mem.Col2.ChainIn E K ι R} (Q : GlobalTheory.Mem.Col2.PerIn I) (emb : ι → E →+* K) (σ : K →+* ℂ), (∀ b, Q.H b = ⊤) → ∀ (w : Q.S'.Cl → Formalism.L2.DIV.Pol ℂ ι (R.N R.m - 1)), (∀ c, w c ∈ Formalism.L2.DIV.VV ℂ Q.sgT) → (∀ c (s : Q.S'.Stab c), w c = (σ (Q.S'.chr c.1 s.1 : K))⁻¹ • Formalism.L2.DIV.rhoP Q.sgT (Formalism.L2.DIV.embGL (Formalism.L2.Col.embAt σ emb) (Q.S'.gam c.1 s.1)) (w c)) → ∃ F : Q.Mt emb σ, ∀ c, F.1 c.1 (Q.S'.rep c) = w c := by
  intro E K ι _ _ _ _ _ _ _ R I Q emb σ _hH w hw hinv
  classical
  let φ : ∀ b, Q.S'.G b → Pol ℂ ι (R.N R.m - 1) → Pol ℂ ι (R.N R.m - 1) := fun b g x =>
    (σ (Q.S'.chr b g : K))⁻¹ • rhoP Q.sgT (embGL (Formalism.L2.Col.embAt σ emb) (Q.S'.gam b g)) x
  have φmul : ∀ b (g h : Q.S'.G b) x, φ b (g * h) x = φ b g (φ b h x) := by
    intro b g h x
    simp only [φ, map_mul, Units.val_mul, mul_inv, Module.End.mul_apply, map_smul, smul_smul]
  have hinv' : ∀ c (s : Q.S'.G c.1), s • Q.S'.rep c = Q.S'.rep c → w c = φ c.1 s (w c) :=
    fun c s hs => hinv c ⟨s, hs⟩
  let F : ∀ b, Q.S'.D b → Pol ℂ ι (R.N R.m - 1) := fun b d => φ b (Q.S'.mv b d) (w (Q.S'.cl b d))
  have hcl : ∀ b (g : Q.S'.G b) (d : Q.S'.D b), Q.S'.cl b (g • d) = Q.S'.cl b d := fun b g d =>
    Sigma.ext rfl (heq_of_eq (Quotient.sound (MulAction.mem_orbit d g)))
  have hlaw : ∀ b (g : Q.S'.G b) d, F b (g • d) = φ b g (F b d) := by
    intro b g d
    set c := Q.S'.cl b d with hc
    have hrep : Q.S'.rep (Q.S'.cl b (g • d)) = Q.S'.rep c :=
      congrArg (Q.S'.rp b) (Quotient.sound (MulAction.mem_orbit d g))
    have h1 : Q.S'.mv b (g • d) • Q.S'.rep c = g • d := by
      convert Q.S'.mv_smul b (g • d) using 2; exact hrep.symm
    have h2 := Q.S'.mv_smul b d
    have hs : ((g * Q.S'.mv b d)⁻¹ * Q.S'.mv b (g • d)) • Q.S'.rep c = Q.S'.rep c := by
      rw [mul_smul, h1, _root_.mul_inv_rev, mul_smul, inv_smul_smul, inv_smul_eq_iff, h2]
    have hw := hinv' c _ hs
    show φ b (Q.S'.mv b (g • d)) (w (Q.S'.cl b (g • d))) = φ b g (φ b (Q.S'.mv b d) (w c))
    rw [hcl, ← φmul]
    conv_rhs => rw [hw, ← φmul, mul_inv_cancel_left]
  refine ⟨⟨F, fun b d => ⟨?_, fun g _ => hlaw b g d⟩⟩, ?_⟩
  · exact Submodule.smul_mem _ _ (polyAction_mem_VV _ _ (hw _))
  · rintro ⟨b, q⟩
    have hq : Q.S'.cl b (Q.S'.rep ⟨b, q⟩) = ⟨b, q⟩ := Sigma.ext rfl (heq_of_eq (Q.S'.rp_spec b q))
    have hr : Q.S'.rep (Q.S'.cl b (Q.S'.rep ⟨b, q⟩)) = Q.S'.rep ⟨b, q⟩ := congrArg (Q.S'.rp b) (Q.S'.rp_spec b q)
    have h1 : Q.S'.mv b (Q.S'.rep ⟨b, q⟩) • Q.S'.rep ⟨b, q⟩ = Q.S'.rep ⟨b, q⟩ := by
      convert Q.S'.mv_smul b (Q.S'.rep ⟨b, q⟩) using 2; exact hr.symm
    show φ b (Q.S'.mv b (Q.S'.rep ⟨b, q⟩)) (w (Q.S'.cl b (Q.S'.rep ⟨b, q⟩))) = w ⟨b, q⟩
    rw [hq]
    exact (hinv' ⟨b, q⟩ _ h1).symm

end GlobalTheory.Mem.Col2.PerIn
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rowForm_prescribed_values_class_representatives : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Formalism.BasicNotions.Ranks} {I : GlobalTheory.Mem.Col2.ChainIn E K ι R} (Q : GlobalTheory.Mem.Col2.PerIn I) (emb : ι → E →+* K) (σ : K →+* ℂ), (∀ b, Q.H b = ⊤) → ∀ (w : Q.S'.Cl → Formalism.L2.DIV.Pol ℂ ι (R.N R.m - 1)), (∀ c, w c ∈ Formalism.L2.DIV.VV ℂ Q.sgT) → (∀ c (s : Q.S'.Stab c), w c = (σ (Q.S'.chr c.1 s.1 : K))⁻¹ • Formalism.L2.DIV.rhoP Q.sgT (Formalism.L2.DIV.embGL (Formalism.L2.Col.embAt σ emb) (Q.S'.gam c.1 s.1)) (w c)) → ∃ F : Q.Mt emb σ, ∀ c, F.1 c.1 (Q.S'.rep c) = w c := by
  atlas_forward_decl GlobalTheory.Mem.Col2.PerIn.exists_Mt_of_rep_values
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coefficientVector_reading_realRepresentation_form : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) {S : (I.rec7 l Z).what₂.Tau → SPar} (MX : DSModel (I.rec7 l Z).sp.X' S) (j : SmT MX →ₗ[ℂ] (Formalism.L2.Forms.FrP (I.rec7 l Z) → ℂ)), GlobalTheory.Core.Rk.Top.IsJ u MX j → ∀ ℓ : SmT MX →ₗ[ℂ] ℂ, ∃ w ∈ Formalism.L2.DIV.VV ℂ (I.perIn u a).sgT, ∀ v, ℓ v = Formalism.L2.DIV.pairB (I.perIn u a).sgT (Formalism.L2.Col.polOf (GlobalTheory.Mem.Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (Formalism.L2.Forms.shiftOf (I.perIn u a).sgT) (GlobalTheory.Mem.Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) (j v)) w := by
  first | exact @GlobalTheory.Core.Rk.Top.exists_pairB_of_isJ | exact GlobalTheory.Core.Rk.Top.exists_pairB_of_isJ | (intros; apply GlobalTheory.Core.Rk.Top.exists_pairB_of_isJ <;> assumption)
end

section
section
noncomputable section

namespace GlobalTheory.AdForm.StabInv

section Pair
open Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.ColAd Matrix

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem lT_fnOf (G : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n) (u : ι → GL (Fin n) ℂ) (P : Pol ℂ ι n) :
    lT G u (fnOf G (shiftOf lam) 1 P) = fnOf G (shiftOf lam) 1 (rhoP lam (invTrK u⁻¹) P) := by
  funext y
  have e1 : ∀ τ, ((invTrK u⁻¹ τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ = (u τ : Matrix (Fin n) (Fin n) ℂ) := fun τ => by
    rw [invTrK_coe, Matrix.transpose_transpose, Pi.inv_apply, inv_inv]
  simp only [lT_apply, fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, Matrix.one_mul, frL, rhoP, MonoidHom.coe_mk,
    OneHom.coe_mk, actP, trAct, detTwK, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_eq_mul, MvPolynomial.smul_eval,
    Formalism.GradedWeylDivisibility.blockAct, eval_aeval_poly, e1, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  have e2 : ∀ τ, detPow ℂ n (invTrK u⁻¹ τ) (lam τ).detShift = (u τ : Matrix (Fin n) (Fin n) ℂ).det ^ (lam τ).detShift :=
    fun τ => by rw [detPow, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.det_transpose, e1]
  simp only [e2, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib, shiftOf, Matrix.mul_apply]
  ring

theorem eq_smul_of_pair (G G' : ι → Matrix (Fin n) (Fin n) ℂ) (lam lam' : ι → DomWeight n) (hl : lam = lam') (o : Frames G')
    (ho : ∀ τ, o.1 τ = 1) (k k' : ι → GL (Fin n) ℂ) (hk : k = k') {w : Pol ℂ ι n} (hw : w ∈ VV ℂ lam) (c : ℂ)
    (h : ∀ φ ∈ ValC G lam', ∃ φ' : Frames G → ℂ, lT G k φ' = φ ∧
      pairB lam (polOf G' (shiftOf lam) o φ') w = c * pairB lam (polOf G' (shiftOf lam) o φ) w) :
    w = c • rhoP lam k' w := by
  subst hl hk
  have hp : ∀ P, polOf G' (shiftOf lam) o (fnOf G (shiftOf lam) 1 P) = P := fun P => by
    have e : (fun τ => (o.1 τ)⁻¹) = 1 := funext fun τ => by rw [ho τ]; exact inv_one
    have := polOf_fnOf G' (shiftOf lam) o P
    rw [e] at this
    exact this
  have hm : w - c • rhoP lam k w ∈ VV ℂ lam := sub_mem hw (Submodule.smul_mem _ _ (polyAction_mem_VV lam k hw))
  have h0 := (pairingBNondegenerate_holds ℂ ι n lam).2 ⟨_, hm⟩ fun P => by
    obtain ⟨φ', e1, e2⟩ := h (lT G k (fnOf G (shiftOf lam) 1 P.1))
      (lT_mem G lam k ⟨P.1, by simpa [MvPolynomial.map_id] using map_mem_CSpan (RingHom.id ℂ) lam _ P.2, rfl⟩)
    have e3 : φ' = fnOf G (shiftOf lam) 1 P.1 := by
      have := congrArg (lT G k⁻¹) e1
      rwa [← lT_mul, ← lT_mul, mul_inv_cancel, lT_one, lT_one] at this
    rw [e3, lT_fnOf, hp, hp] at e2
    have e4 := pairingBInvariantK_holds ℂ ι n lam k⁻¹ P.1 (rhoP lam k w)
    have e5 : actP lam k⁻¹ (rhoP lam k w) = w := by
      show (rhoP lam k⁻¹ * rhoP lam k) w = w
      rw [← map_mul, inv_mul_cancel, map_one]; rfl
    rw [e5] at e4
    rw [pairBK_apply]
    show pairB lam P.1 (w - c • rhoP lam k w) = 0
    rw [map_sub, map_smul, e2, ← e4, smul_eq_mul]
    exact sub_self _
  exact sub_eq_zero.1 (congrArg Subtype.val h0)

end Pair

section Law
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
  Formalism.L2.Forms GlobalTheory.Core.Rk GlobalTheory.Core.Rk.Top GlobalTheory.Core.Rk.TopOnto
open GlobalTheory.Mem.ColAd GlobalTheory.Core.Rk.TopLift GlobalTheory.Core.Rk.Top.Model GlobalTheory.PointAtPlaceHom Formalism.MainNotions.StandardLattice Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u : D.what₂.Word} {θ : InfFam D} {S : D.what₂.Tau → SPar} {M : DSModel D.sp.X' S}
  {j : SmT M →ₗ[ℂ] (FrP D → ℂ)} {J : Set (GA D D.sp.X')} {χ : GA D D.sp.X' → ℂ}

set_option maxHeartbeats 1000000 in

theorem coset_law_moved (hθ : IsInfFam θ) (hj : IsJ u M j) {b : GA D D.sp.X'} (hb : b ∈ GfC D.sp.X') {γ : GA D D.sp.X'}
    (hγ : γ ∈ GQ D.sp.X') {k h h' : GA D D.sp.X'} {κ x x'} (hk : HasMat k κ) (hJ : b⁻¹ * k * b ∈ J) (hh : HasMat h x)
    (hh' : HasMat h' x') (e : x' = (finPt γ).1 * x * κ) (v : SmT M) :
    ∃ v' : SmT M, lT _ (infPt θ γ) (j v') = j v ∧
      ∀ T ∈ MultT θ M J χ, T v' (h' * b) = χ (b⁻¹ * k * b) * T v (h * b) := by
  have R := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ D.sp.X'
  obtain ⟨f, hf, a, ha, rfl⟩ := R.2.2.2.2.2.2.1 γ
  obtain ⟨v', e1, e2⟩ := real_translate (J := J) (χ := χ) hθ hj a ha v
  have e3 : h' = f * h * k := by
    refine hasMat_pt hh' ?_
    have := hasMat_finPt (mul_mem (mul_mem hf hh.1) hk.1)
    rwa [finPt_mul, finPt_mul, finPt_of_hasMat hh, finPt_of_hasMat hk, ← finPt_mul_inf f ha, ← e] at this
  refine ⟨v', by rw [map_mul (infPt θ), infPt_of_fin θ hf, one_mul, e1], fun T hT => ?_⟩
  have e4 : h' * b * a = f * a * (h * b * (b⁻¹ * k * b)) := by
    have e5 : h * b * (b⁻¹ * k * b) = h * k * b := by group
    rw [e5, e3, mul_assoc f a, comm_of_mem _ ha (mul_mem (mul_mem hh.1 hk.1) hb)]
    simp only [mul_assoc]
  rw [e2 T hT, e4, multT_rel' (h * b * (b⁻¹ * k * b)) (f * a * (h * b * (b⁻¹ * k * b))) 1 (fun m hm w => by
    rw [one_mul]; exact (hm.aut w).left _ hγ _) hT, one_mul,
    multT_rel' (h * b) (h * b * (b⁻¹ * k * b)) (χ (b⁻¹ * k * b)) (fun m hm w => hm.lev w _ hJ (h * b)) hT]

end Law

section Chi
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2
  GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem chi_eq_chr {B : Base} {X : PreX B.toPre} (I : TC B X) (a : I.ι) {Lb U chi y lat st} (hR : I.ReadsP a Lb U chi y lat st)
    (c : (I.stX a).Cl) (s : (I.stX a).Stab c) (κ : U)
    (e' : y c = bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) ((I.stX a).gam c.1 s.1) * y c * κ.1) :
    ((chi κ : ℂˣ) : ℂ) = B.embLL (((I.stX a).chr c.1 s.1 : B.LLˣ) : B.LL) := by
  let κ0 : (I.stX a).G c.1 := (1, s.1.2.1, s.1.2.2)
  have hgam : (I.stX a).gam c.1 κ0 = 1 := map_one (ufGL B.fields.E (B.R.N B.R.m - 1))
  have hp := GlobalTheory.Mem.Col2.TilX.isPtOf_rat (hR.pt c) (s.1.1)⁻¹
  have hact : ((I.stX a).act c.1 κ0 ((I.stX a).rep c)).1.1 = (((s.1.1)⁻¹, 1, 1) : UF B.fields.E (B.R.N B.R.m - 1) ×
      GLG B.fields.E (B.R.N B.R.m - 1) (B.primes X).vGs × GLQ B.fields.E (B.R.N B.R.m - 1) (QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K))) •
      ((I.stX a).rep c).1.1 := by
    have e1 : FrmG.incl _ _ s.1 • ((I.stX a).rep c).1.1 = ((I.stX a).rep c).1.1 :=
      congrArg (fun d : (I.stX a).D c.1 => d.1.1) s.2
    conv_rhs => rw [← e1]
    refine Eq.trans ?_ (smul_smul _ _ _).symm
    have e2 : FrmG.incl _ _ κ0 = (((s.1.1)⁻¹, 1, 1) : UF B.fields.E (B.R.N B.R.m - 1) ×
        GLG B.fields.E (B.R.N B.R.m - 1) (B.primes X).vGs × GLQ B.fields.E (B.R.N B.R.m - 1) (QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K))) *
        FrmG.incl _ _ s.1 := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · exact (inv_mul_cancel _).symm
      · exact (one_mul _).symm
      · exact (one_mul _).symm
    exact congrArg (fun t => t • ((I.stX a).rep c).1.1) e2
  have hyk : y c * κ.1 = ratAd B.host.F (s.1.1)⁻¹ * y c := by
    have e3 : ratAd B.host.F (s.1.1)⁻¹ =
        (bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) ((I.stX a).gam c.1 s.1))⁻¹ := by
      unfold ratAd
      rw [map_inv, map_inv]
      rfl
    rw [e3]
    conv_rhs => rw [e']
    group
  have hq : PtOf (y c * κ.1) ((I.stX a).act c.1 κ0 ((I.stX a).rep c)).1.1 := by
    rw [hyk, hact]
    exact hp
  exact hR.chr c κ κ0 hgam hq

theorem sgT_eq {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) :
    (I.perIn u a).sgT = (Formalism.L2.Forms.sgT (D := I.rec7 l Z) u : B.fields.Tau → DomWeight (B.R.N B.R.m - 1)) := by
  funext τ
  obtain ⟨a, ha⟩ := B.R.t_odd
  have e1 : B.R.m * (B.R.t + 1) / 2 = B.R.m * (a + 1) := by
    rw [ha, show B.R.m * (2 * a + 1 + 1) = 2 * (B.R.m * (a + 1)) by ring]; omega
  have e2 : (B.R.t + 1) / 2 = a + 1 := by omega
  show GlobalTheory.Mem.Col2.shW (B.wts.sgW τ) (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))) =
    Formalism.L2.Forms.shW (B.wts.sgW τ) ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ)
  rw [e1, e2]
  unfold GlobalTheory.Mem.Col2.shW Formalism.L2.Forms.shW
  congr 1

theorem star_eq_inv {H K : Type} [Group H] [Finite H] [Field K] (φ : H →* Kˣ) (σ : K →+* ℂ) (s : H) :
    star (σ (φ s : K)) = (σ (φ s : K))⁻¹ := by
  have e : σ (φ s : K) ^ Nat.card H = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one, map_one]
  exact (Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one e Nat.card_pos.ne')).symm

end Chi

section Main
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.TopLift GlobalTheory.Core.Rk.TopOnto GlobalTheory.Core.Rk.Top.Model

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem reading_stab_inv : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ : ℕ → ℂ), PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (a : I.ι), ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → ∀ f : CXP R P t, ∀ (c : (I.stX a).Cl) (w : Formalism.L2.DIV.Pol ℂ (I.rec7 l Z).what₂.Tau (B.R.N B.R.m - 1)), w ∈ Formalism.L2.DIV.VV ℂ (I.perIn u a).sgT → (∀ v h, GlobalTheory.Core.Rk.Top.HasMat h (K.y c).1 → f.1 v (h * g.bT) = Formalism.L2.DIV.pairB (I.perIn u a).sgT (Formalism.L2.Col.polOf (GlobalTheory.Mem.Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (Formalism.L2.Forms.shiftOf (I.perIn u a).sgT) (GlobalTheory.Mem.Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) (j v)) w) → ∀ s : (I.stX a).Stab c, w = (B.embLL ((I.stX a).chr c.1 s.1 : B.LL))⁻¹ • Formalism.L2.DIV.rhoP (I.perIn u a).sgT (Formalism.L2.DIV.embGL (Formalism.L2.Col.embAt B.embLL B.fields.emb) ((I.stX a).gam c.1 s.1)) w := by
  intro B X I hI hP l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ hX j hj P t a bad K hR hb hL f c w hw hf s
  have hθ : IsInfFam R.θ := hX.inf
  have hst : (K.stabI c s).1 = (I.stX a).gam c.1 s.1 := hR.stab c s
  obtain ⟨κ₀, hκ₀, e0⟩ := (K.stabI_range c (K.stabI c s)).1 ⟨s, rfl⟩
  let κ : K.lev.U := ⟨κ₀, hκ₀⟩⁻¹
  have e1 : (K.y c).1 = Formalism.UG.bc (Formalism.UG.inclE (F := (I.rec7 l Z).host.F)
      (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) (K.stabI c s).1 * (K.y c).1 * κ.1 := by
    rw [← e0]
    show _ = (K.y c).1 * κ₀ * (K.y c).1⁻¹ * (K.y c).1 * κ₀⁻¹
    group
  have e2 := chi_eq_chr I a hR c s κ (by
    have h0 := e1
    rw [hst] at h0
    exact h0)
  haveI : Finite ((I.stX a).Stab c) := ((I.fm l u a).stabPFin c : Finite _)
  have e3 := star_eq_inv (((I.stX a).chr c.1).comp (Subgroup.subtype _ : (I.stX a).Stab c →* _)) B.embLL s
  obtain ⟨γ, hγ, e4, e5⟩ := exists_ratPt hθ (rankP (I.rec7 l Z)) (K.stabI c s).1 (K.stabI c s).2
  obtain ⟨k, hk⟩ := hasMat_exists (D := I.rec7 l Z) ⟨κ.1, ((K.lev.U_eq _).1 κ.2).1⟩
  obtain ⟨h, hh⟩ := hasMat_exists (D := I.rec7 l Z) (K.y c)
  have e6 : levChi _ R.βX (datXP R P t) (g.bT⁻¹ * k * g.bT) = (B.embLL ((I.stX a).chr c.1 s.1 : B.LL))⁻¹ :=
    (hL.2 k κ hk).trans ((congrArg star e2).trans e3)
  refine eq_smul_of_pair (gramC (gramP (I.rec7 l Z)) (embT (I.rec7 l Z))) _ _ _ (sgT_eq I l Z u a)
    (GlobalTheory.Mem.Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) (fun _ => rfl) (infPt R.θ γ) _ ?_ hw _ fun φ hφ => ?_
  · funext τ
    refine Units.ext ((e5 τ).trans ?_)
    rw [hst]
    ext p q
    show B.host.φ₀ _ = _
    rw [← B.embE_φ₀]
    rfl
  · obtain ⟨v, rfl⟩ := (hj.range ▸ hφ : φ ∈ LinearMap.range j)
    obtain ⟨v', e7, e8⟩ := coset_law_moved (χ := levChi _ R.βX (datXP R P t)) hθ hj hb hγ hk ((hL.1 k).2 ⟨κ, hk⟩) hh hh
      (e1.trans (congrArg (· * (K.y c).1 * κ.1) e4.symm)) v
    refine ⟨j v', e7, ?_⟩
    have e9 := e8 f.1 f.2
    rw [hf v' h hh, hf v h hh, e6] at e9
    exact e9

end Main

end GlobalTheory.AdForm.StabInv

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.readingVector_fixed_by_class_stabiliser_character : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ : ℕ → ℂ), PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (a : I.ι), ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → ∀ f : CXP R P t, ∀ (c : (I.stX a).Cl) (w : Formalism.L2.DIV.Pol ℂ (I.rec7 l Z).what₂.Tau (B.R.N B.R.m - 1)), w ∈ Formalism.L2.DIV.VV ℂ (I.perIn u a).sgT → (∀ v h, GlobalTheory.Core.Rk.Top.HasMat h (K.y c).1 → f.1 v (h * g.bT) = Formalism.L2.DIV.pairB (I.perIn u a).sgT (Formalism.L2.Col.polOf (GlobalTheory.Mem.Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (Formalism.L2.Forms.shiftOf (I.perIn u a).sgT) (GlobalTheory.Mem.Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) (j v)) w) → ∀ s : (I.stX a).Stab c, w = (B.embLL ((I.stX a).chr c.1 s.1 : B.LL))⁻¹ • Formalism.L2.DIV.rhoP (I.perIn u a).sgT (Formalism.L2.DIV.embGL (Formalism.L2.Col.embAt B.embLL B.fields.emb) ((I.stX a).gam c.1 s.1)) w := by
  atlas_forward_decl GlobalTheory.AdForm.StabInv.reading_stab_inv
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.AdForm.exists_readsG_of_level : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ : ℕ → ℂ), PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (a : I.ι), ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → ∀ f : CXP R P t, ∃ G', ReadsG K eW j g.bT G' f.1 := by
  intro B X I hI hP l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ hX j hj P t a bad K eW hR heW hb hL f

  have hv : ∀ c : (I.stX a).Cl, ∃ w ∈ Formalism.L2.DIV.VV ℂ (I.perIn u a).sgT, ∀ v h, GlobalTheory.Core.Rk.Top.HasMat h (K.y c).1 →
      f.1 v (h * g.bT) = Formalism.L2.DIV.pairB (I.perIn u a).sgT (Formalism.L2.Col.polOf (GlobalTheory.Mem.Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (Formalism.L2.Forms.shiftOf (I.perIn u a).sgT) (GlobalTheory.Mem.Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) (j v)) w := by
    intro c
    obtain ⟨h₀, hh₀⟩ := GlobalTheory.Core.Rk.Top.Model.hasMat_exists (D := I.rec7 l Z) (K.y c)
    obtain ⟨w, hw, e⟩ := GlobalTheory.T.exists_coefficientVector_reading_realRepresentation_form I l Z u a R.MX j hj ((LinearMap.proj (h₀ * g.bT)).comp f.1)
    refine ⟨w, hw, fun v h hh => ?_⟩
    rw [GlobalTheory.Core.Rk.Top.Model.hasMat_pt hh hh₀]
    exact e v
  choose w hw hwv using hv
  obtain ⟨G', hG'⟩ := GlobalTheory.T.exists_rowForm_prescribed_values_class_representatives (I.perIn u a) B.fields.emb B.embLL (fun _ => rfl) w hw
    (fun c s => GlobalTheory.T.readingVector_fixed_by_class_stabiliser_character I hI hP l Z u R g c₀ hX j hj P t a bad K hR hb hL f c (w c) (hw c) (hwv c) s)
  refine ⟨G', fun c v h hh => ?_⟩
  rw [hwv c v h hh]
  have hz : ∀ c', eW.symm (Pi.single c (j v)) c' = (Pi.single c (j v) : (I.fm l u a).clsP → Formalism.L2.Forms.FrP (I.rec7 l Z) → ℂ) c' := by
    intro c'
    funext y'
    have := heW (eW.symm (Pi.single c (j v))) c' y' y' rfl
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  generalize eW.symm (Pi.single c (j v)) = z at hz
  have hzc : z c = j v := by rw [hz c, Pi.single_eq_same]
  have hzo : ∀ c', c' ≠ c → z c' = 0 := fun c' h => by
    rw [hz c']
    exact Pi.single_eq_of_ne h _
  haveI := (l.per u a).step.fin_stab c.1 ((I.perIn u a).S'.rep c)
  have hne : ((Nat.card ((I.perIn u a).S'.Stab c) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  letI := (I.perIn u a).clFin (l.per u a)
  show _ = _ * (∑ c' : (I.perIn u a).S'.Cl, (I.perIn u a).wt c' • (Formalism.L2.DIV.pairB (K := ℂ) (I.perIn u a).sgT).compl₁₂
      (Formalism.L2.Col.polOf (GlobalTheory.Mem.Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (Formalism.L2.Forms.shiftOf (I.perIn u a).sgT)
        (GlobalTheory.Mem.Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) ∘ₗ LinearMap.proj c')
      (LinearMap.proj c' ∘ₗ (I.perIn u a).rd B.fields.emb B.embLL)) z G'
  rw [LinearMap.sum_apply, LinearMap.sum_apply]
  erw [Fintype.sum_eq_single c (fun c' hc' => by
    change (I.perIn u a).wt c' * Formalism.L2.DIV.pairB _ (Formalism.L2.Col.polOf _ _ _ (z c')) _ = 0
    rw [hzo c' hc']
    simp only [map_zero, LinearMap.zero_apply, mul_zero])]
  change _ = _ * ((((Nat.card ((I.perIn u a).S'.Stab c) : ℕ) : ℂ)⁻¹) * Formalism.L2.DIV.pairB _ (Formalism.L2.Col.polOf _ _ _ (z c)) (G'.1 c.1 ((I.perIn u a).S'.rep c)))
  rw [hzc, hG' c, ← mul_assoc]
  erw [mul_inv_cancel₀ hne, one_mul]
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rowForm_reading_levelForm_lastSpace : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ : ℕ → ℂ), PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (a : I.ι), ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → ∀ f : CXP R P t, ∃ G', ReadsG K eW j g.bT G' f.1 := by
  atlas_forward_decl GlobalTheory.AdForm.exists_readsG_of_level
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.MiS GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm

set_option maxHeartbeats 2000000 in

theorem clsPinD_of_famCol : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : (I.rec7 l Z).what₂.Word) (f : FamCh W u), TrueW W → TwStd W → TopReadAt W u f.j f.g.bT → f.RowOK → FamCol f → ClsPinD f.t := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W u f hTW hStd hTop hRow hCol
  obtain ⟨c₀, hX, hcol⟩ := hCol
  have hOk := hTW.ok
  have hPins := hTW.pins.some
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_nonzero_jetScale_trueColumns I hOk hPins l Z (pk W).ψ (pk W).θ hX.std hX.inf
  obtain ⟨J, hJ⟩ := GlobalTheory.T.exists_translates_of_values_frames I hOk hPins l Z (pk W) hX.inf f.j
  have hemb : IsEmbTop (D := I.rec7 l Z) (TC.z0 X u) ((f.g.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _)) := by
    obtain ⟨UT, ε, hP⟩ := (hcol W.P.A3.A.μ0).2
    exact hP.emb
  refine ⟨realOf u (pk W) f.g s J, GlobalTheory.T.trueColumns_realData_spec I hOk hPins l Z u (pk W) f.g c₀ s J hX f.j hTop.1 hJ hemb, fun t => ⟨?_, ?_⟩⟩
  · obtain ⟨⟨Ch₀, A, ι, w, hA⟩, -⟩ := hcol t
    exact ⟨_, GlobalTheory.T.kernelPart_laws_of_columnPins I hOk hPins l Z u (pk W) f.g c₀ s J hX hs hRow.x (lvP W) t (f.row t) (W.P.I.tup t) (f.col t) _ Ch₀ A ι w hA⟩
  · obtain ⟨⟨Ch₀, A, ι, w, hA⟩, UT, ε, hTL⟩ := hcol t
    have hstdC := hTW.std.some
    have key : ∀ a : (I.rec7 l Z).what₂.Tup, LevAt W u a f.g.bT (levS _ (pk W).βX (datXP (pk W) (lvP W) t)) (levChi _ (pk W).βX (datXP (pk W) (lvP W) t)) →
        ∃ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := I.rec7 l Z) (u := u) (I.fm l u a) bad)
          (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)),
          I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) ∧
          (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') ∧
          LevG K f.g.bT (levS _ (pk W).βX (datXP (pk W) (lvP W) t)) (levChi _ (pk W).βX (datXP (pk W) (lvP W) t)) ∧
          ∀ (ψ : ColT I l u a B.R.m) (F : CXP (pk W) (lvP W) t), ∃ G', ReadsG K eW f.j f.g.bT G' F.1 ∧
            tailOf W u f.j f.g.bT a ψ F.1 = (I.per l u a).Ptil ψ G' := by
      intro a hL
      by_cases h0 : a = I.mu0
      · subst h0
        have hon := GlobalTheory.T.exists_rowForm_reading_levelForm_lastSpace I hOk hPins l Z u (pk W) f.g c₀ hX f.j hTop.1 (lvP W) t I.mu0 _ (W.R.T.cols.forms u).clsP.toG
          (W.R.T.cols.forms u).valP.eW (hstdC u).what₂ (hstdC u).eW hTop.2.1 (hL.1 rfl)
        refine ⟨_, (W.R.T.cols.forms u).clsP.toG, (W.R.T.cols.forms u).valP.eW, (hstdC u).what₂, (hstdC u).eW, hL.1 rfl, ?_⟩
        intro ψ F
        have hex : ∃ G, Reads W u f.j f.g.bT I.mu0 G F.1 := by
          obtain ⟨G', hG'⟩ := hon F
          refine ⟨(I.rec7 l Z).eMt u G', fun h => ?_, fun h => absurd rfl h⟩
          have e : ((I.rec7 l Z).eMt u).symm (h ▸ ((I.rec7 l Z).eMt u) G') = G' := ((I.rec7 l Z).eMt u).symm_apply_apply G'
          first
            | (rw [e]; exact hG')
            | exact e ▸ hG'
            | exact (congrArg (fun G => ReadsG (W.R.T.cols.forms u).clsP.toG (W.R.T.cols.forms u).valP.eW f.j f.g.bT G F.1) e).mpr hG'
        refine ⟨_, hex.choose_spec.1 rfl, ?_⟩
        unfold tailOf
        rw [dif_pos hex]
        split
        · rfl
        · next h => exact absurd rfl h
      · obtain ⟨l0, t', e, hh, hst⟩ := hStd
        obtain ⟨-, -, hP⟩ := hst
        cases ex
        dsimp only at e
        subst e
        have hh' := eq_of_heq hh
        subst hh'
        have hon := GlobalTheory.T.exists_rowForm_reading_levelForm_lastSpace I hOk hPins l Z u (pk W) f.g c₀ hX f.j hTop.1 (lvP W) t a _ (W.R.T.tw.pt.cls u a h0)
          (W.R.T.tw.pt.val u a h0).eW (hP.what₂ u a h0) (hP.eW u a h0) hTop.2.1 (hL.2 h0)
        refine ⟨_, W.R.T.tw.pt.cls u a h0, (W.R.T.tw.pt.val u a h0).eW, hP.what₂ u a h0, hP.eW u a h0, hL.2 h0, ?_⟩
        intro ψ F
        have hex : ∃ G, Reads W u f.j f.g.bT a G F.1 := by
          obtain ⟨G', hG'⟩ := hon F
          refine ⟨(I.rec7 l Z).eMtTw u a G', fun h => absurd h h0, fun h => ?_⟩
          have e := ((I.rec7 l Z).eMtTw u a).symm_apply_apply G'
          first
            | (rw [e]; exact hG')
            | exact e ▸ hG'
            | exact (congrArg (fun G => ReadsG (W.R.T.tw.pt.cls u a h0) (W.R.T.tw.pt.val u a h0).eW f.j f.g.bT G F.1) e).mpr hG'
        refine ⟨_, hex.choose_spec.2 h0, ?_⟩
        unfold tailOf
        rw [dif_pos hex]
        split
        · next h => exact absurd h h0
        · rfl
    obtain ⟨bad, K, eW, h1, h2, h3, h4⟩ := key _ (hTop.2.2 t).1
    exact GlobalTheory.T.exists_lastPeriod_classData_of_lastStep I hOk hPins l Z u (pk W) f.g c₀ s J hX f.j hTop.1 hJ (lvP W) t (f.row t) (W.P.I.tup t) (f.col t) _ Ch₀ A ι w hA UT ε hTL bad K eW h1 h2 hTop.2.1 h3 h4

end GlobalTheory.AdForm
end
