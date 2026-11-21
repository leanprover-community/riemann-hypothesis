import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicTypeOfSmoothBorelKilledStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelUnitaryIrreducibleOrthonormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFrameBorelActsExtremalVectorByWeightStatement
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsSubspaceStableSobolevFormDerivStatement
import BuildAid.ForwardExisting

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.MultDer

theorem rderC_eq : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsMultMap θ M J χ T → ∀ (v : M.Vec) (τ : D.what₂.Tau) (Z : Mt V.rank) (y : M.sm τ), (y : M.H τ) = dRepC (gramAt D V τ) (M.rep τ) Z (v τ : M.H τ) → RderC θ V τ Z (T v) = T (Function.update v τ y) := by
  intro D θ V _ S M J χ T hT v τ Z y hy
  obtain ⟨hc, hU, -⟩ := GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ
  have hu := GlobalTheory.SmoothAutCheck.gramAt_unit V τ
  obtain ⟨hsp, hsm⟩ := GlobalTheory.T.smoothVectors_subspace_stable_sobolevForm_deriv V.rank (gramAt D V τ) (M.H τ) (M.rep τ)
    (GlobalTheory.SmoothAutCheck.gramAt_herm V τ) hu.ne_zero hU
  have hv : SmoothVec (lieH (gramAt D V τ)) (M.rep τ) (v τ : M.H τ) := hsp _ (v τ).2
  obtain ⟨h1, -, -, h4⟩ := hsm _ hv
  funext g
  obtain ⟨ℓ, hℓ, hval⟩ := hT.cont τ v g
  have key : ∀ X ∈ lieAt V τ, Rder θ V τ X (T v) g = ℓ (dRep (M.rep τ) X (v τ : M.H τ)) := by
    intro X hX
    have e : (fun t : ℝ => T v (g * oneP θ V τ X t)) =
        fun t : ℝ => ℓ (M.rep τ (NormedSpace.exp (t • X)) (v τ : M.H τ)) := by
      funext t
      have hm := GlobalTheory.SmoothAutCheck.exp_mem_UH hu hX t
      let w : M.sm τ := ⟨M.rep τ (NormedSpace.exp (t • X)) (v τ : M.H τ), Submodule.subset_span (h1 _ hm)⟩
      have h := congrFun (hT.equiv τ _ hm v w rfl) g
      exact ((hval w).trans h).symm
    unfold Rder
    rw [e]
    exact (h4 ℓ hℓ X hX).deriv
  obtain ⟨p1, p2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
  have h := hval y
  rw [hy] at h
  refine Eq.trans ?_ h
  unfold RderC dRepC
  rw [Pi.add_apply, Pi.smul_apply, key _ p1, key _ p2, map_add, map_smul]
  rfl

end GlobalTheory.MultDer
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicityMap_complexRightDerivative_eq : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsMultMap θ M J χ T → ∀ (v : M.Vec) (τ : D.what₂.Tau) (Z : Mt V.rank) (y : M.sm τ), (y : M.H τ) = dRepC (gramAt D V τ) (M.rep τ) Z (v τ : M.H τ) → RderC θ V τ Z (T v) = T (Function.update v τ y) := by
  atlas_forward_decl GlobalTheory.MultDer.rderC_eq
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MultHol

section Local

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {Hm : ι → Mt n}

omit [Fintype ι] [DecidableEq ι] in
theorem one_mem_UG : (1 : ι → Mt n) ∈ UG Hm := fun τ => by
  show (1 : Mt n)ᴴ * Hm τ * 1 = Hm τ
  simp

omit [Fintype ι] [DecidableEq ι] in
theorem mul_mem_UG {u u' : ι → Mt n} (hu : u ∈ UG Hm) (hu' : u' ∈ UG Hm) : u * u' ∈ UG Hm := fun τ => by
  have h1 : (u τ)ᴴ * Hm τ * u τ = Hm τ := hu τ
  have h2 : (u' τ)ᴴ * Hm τ * u' τ = Hm τ := hu' τ
  show (u τ * u' τ)ᴴ * Hm τ * (u τ * u' τ) = Hm τ
  calc _ = (u' τ)ᴴ * ((u τ)ᴴ * Hm τ * u τ) * u' τ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Hm τ := by rw [h1, h2]

omit [Fintype ι] in
theorem mulSingle_mem_UG (τ : ι) {g : Mt n} (hg : g ∈ Formalism.QuantumDeterminants.UH (Hm τ)) :
    (Pi.mulSingle τ g : ι → Mt n) ∈ UG Hm := fun ρ => by
  by_cases h : ρ = τ
  · subst h; simpa using hg
  · rw [Pi.mulSingle_eq_of_ne h]; exact one_mem_UG (Hm := Hm) ρ

omit [Fintype ι] [DecidableEq ι] in
theorem lift_prod {G : Type} [Group G] (L : (ι → Mt n) → G)
    (hL : ∀ u ∈ UG Hm, ∀ u' ∈ UG Hm, L (u * u') = L u * L u') (l : List (ι → Mt n)) (hl : ∀ u ∈ l, u ∈ UG Hm) :
    l.prod ∈ UG Hm ∧ L l.prod = (l.map L).prod := by
  induction l with
  | nil =>
    refine ⟨one_mem_UG, ?_⟩
    have h := hL 1 one_mem_UG 1 one_mem_UG
    rw [mul_one] at h
    simpa using h
  | cons a l ih =>
    have ha := hl a (List.mem_cons_self ..)
    obtain ⟨h1, h2⟩ := ih fun u hu => hl u (List.mem_cons_of_mem _ hu)
    rw [List.prod_cons, List.map_cons, List.prod_cons]
    exact ⟨mul_mem_UG ha h1, by rw [hL a ha _ h1, h2]⟩

theorem parts_mem_lieH {G : Mt n} (hh : G.IsHermitian) (hd : G.det ≠ 0) (Z : Mt n) :
    (1 / 2 : ℂ) • (Z + conjH G Z) ∈ lieH G ∧ (1 / (2 * Complex.I)) • (Z - conjH G Z) ∈ lieH G := by
  have hu : IsUnit G.det := isUnit_iff_ne_zero.2 hd
  have e1 : G * conjH G Z = -(Zᴴ * G) := by
    rw [conjH, Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
  have e2 : (conjH G Z)ᴴ * G = -(G * Z) := by
    have := congrArg conjTranspose e1
    simpa only [conjTranspose_mul, conjTranspose_neg, conjTranspose_conjTranspose, hh.eq] using this
  constructor
  · show _ + _ = _
    have s : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [conjTranspose_smul, s, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, conjTranspose_add, Matrix.add_mul,
      Matrix.mul_add, e1, e2]
    simp
  · show _ + _ = _
    have s : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
      simp
    rw [conjTranspose_smul, s, Matrix.smul_mul, Matrix.mul_smul, neg_smul, ← smul_neg, ← smul_add, conjTranspose_sub,
      Matrix.sub_mul, Matrix.mul_sub, e1, e2]
    have : -(Zᴴ * G - -(G * Z)) + (G * Z - -(Zᴴ * G)) = 0 := by abel
    rw [this, smul_zero]

end Local

theorem holAd_of_isMultMap : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → ∀ (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsMultMap θ M J χ T → HolAd θ M w (T v) := by
  classical
  intro D θ V S M w v hθ hS hw hv J χ T hT g
  obtain ⟨L, -, hmul, -, -, hinv, hat, -, -, hG⟩ := GlobalTheory.RealLift.exists_real_lift D θ V hθ
  have hexp : ∀ τ, ∀ X ∈ lieH (gramAt D V τ), ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) :=
    fun τ X hX t => GlobalTheory.SmVec.exp_mem_UH ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hG τ).2)) hX t
  have hone : ∀ τ, ∀ X ∈ lieH (gramAt D V τ), ∀ t : ℝ,
      L (Pi.mulSingle τ (NormedSpace.exp (t • X))) = oneP θ V τ X t :=
    fun τ X hX t => (hat τ _ (hexp τ X hX t)).symm
  refine ⟨fun u => T v (g * L u), ?_, fun u hu => by simp only [hinv u hu]⟩
  refine GlobalTheory.T.holomorphicType_of_smooth_borelKilled _ _ _ _ _ _ (fun τ => ((GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.2.2 hS).1) _ ?_ ?_
  · intro k τs Xs hX u hu
    have h := (hT.aut v).smooth k τs Xs hX (g * L u)
    convert h using 2 with t
    obtain ⟨h1, h2⟩ := lift_prod L hmul
      (List.ofFn fun i => (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : D.what₂.Tau → Mt V.rank)) (by
        intro x hx
        obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
        exact mulSingle_mem_UG _ (hexp _ _ (hX i) _))
    show T v (g * L (u * _)) = _
    rw [hmul u hu _ h1, h2, List.map_ofFn, mul_assoc]
    exact congrArg (fun F : Fin k → GA D V => T v (g * (L u * (List.ofFn F).prod))) (funext fun i => hone _ _ (hX i) _)
  · intro τ a c hac u hu
    have hder : ∀ X ∈ lieH (gramAt D V τ), der τ X (fun u => T v (g * L u)) u = Rder θ V τ X (T v) (g * L u) := by
      intro X hX
      unfold der Rder
      congr 1
      funext t
      show T v (g * L (u * _)) = _
      rw [hmul u hu _ (mulSingle_mem_UG _ (hexp _ _ hX _)), hone τ X hX, mul_assoc]
    obtain ⟨p1, p2⟩ := parts_mem_lieH (hG τ).1 (hG τ).2 (x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹)
    have hk := (GlobalTheory.T.baseFrameBorel_acts_extremalVector_by_weight D θ V S M w v hθ hS hw hv τ).2 a c hac
    have hd := GlobalTheory.T.multiplicityMap_complexRightDerivative_eq D θ V hθ S M J χ T hT v τ (x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹)
      (if a = c then (w τ a : ℂ) • v τ else 0) (by rw [hk]; split_ifs <;> rfl)
    have e : derC (gramAt D V) τ (x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹) (fun u => T v (g * L u)) u =
        RderC θ V τ (x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹) (T v) (g * L u) := by
      unfold derC
      rw [hder _ p1, hder _ p2]
      rfl
    rw [e, hd]
    split_ifs
    · rw [T.map_update_smul, Function.update_eq_self]
      rfl
    · rw [T.map_update_zero]
      rfl

end GlobalTheory.MultHol
end
end
