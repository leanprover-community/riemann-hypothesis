import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFramesStrongApproximation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainDataPrincipalCongruenceLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneTorusClassNumberBoundProof
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDetIsTA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivalenceGeneratedTorusRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaTermTsumLeTwo
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogClassNumberLeLogAbsDiscrDiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelIndexBoundOfPrintsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsInertPlOfInertOff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousEquivariantDetOneFactorProjectio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupMeasureDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainOrthonormalFrameIdentification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousRealComponentHomUnitaryAdelicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureTranslateLevelRealBoxLeIndexMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentRepresentativesInjectiveDoubleCoset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePartMemFullLevelOfKeepsSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceConjMemArithmeticGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCongruenceIffCompletion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignatureUnitaryLatticeFamily
import BuildAid.ForwardExisting

section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_group_measure_decomposition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) [Fintype κ] (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r) (a₀ : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ)) (π : (∀ ρ, UpqT (p ρ) (q ρ)) → realSU Ψ G) (m : ∀ ρ, Measure (UpqT (p ρ) (q ρ))), 1 ≤ r → 1 ≤ Ψ.card → IsIdent p q Ψ G x σ A e → Continuous π → IsProj p q Ψ G σ A a₀ π → (∀ (s : realSU Ψ G) (b₀ : ∀ ρ, UpqT (p ρ) (q ρ)), (∀ ρ, UpqT.mat (b₀ ρ) * A ρ = A ρ * ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) → ∀ b, π (b₀ * b) = s * π b) → (∀ ρ, IsMinf (m ρ)) → ∀ S : Set (realSU Ψ G), MeasurableSet S → Measure.pi m (π ⁻¹' S) ≤ ENNReal.ofReal ((1000 * (Ψ.card : ℝ) * (r : ℝ) ^ 3) ^ (Ψ.card * r ^ 2)) * riemHaar Ψ G x S := by
  first | exact @GlobalTheory.CovTop.VolUp.MassUp.massUp | exact GlobalTheory.CovTop.VolUp.MassUp.massUp | (intros; apply GlobalTheory.CovTop.VolUp.MassUp.massUp <;> assumption)
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CovTop.VolUp.Reps

theorem isKM_one_of_three {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (c : Gal(E/F)) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (k : Matrix (Fin n) (Fin n) (RA F E))
    (h : IsKM c G L 3 k) : IsKM c G L 1 k := by
  refine ⟨h.1, fun x hx => ?_, h.2.2⟩
  obtain ⟨y, hy, e⟩ := h.2.1 x hx
  exact ⟨3 • y, nsmul_mem hy 3, by rw [e, one_smul]⟩

theorem exists_reps : ∀ (D : D7) (V : HSp D) (Λ : Set (Fin V.rank → D.host.E)) (K₀ : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))), IsOpen {h : GA D V | finE V h ∈ K₀} → (∀ h : GA D V, IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) Λ 1 ((finHom V h).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) → finE V h ∈ K₀) → ∃ (J : Type) (_ : Countable J) (g : J → GA D V), (∀ j, g j ∈ GfC V) ∧ (∀ i j, UEquiv (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) Λ 3 ((finHom V (g i)).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) ((finHom V (g j)).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) → i = j) ∧ ∀ h : GA D V, ∃ j, ∃ γ ∈ GQ V, finE V ((g j)⁻¹ * γ * h) ∈ K₀ := by
  intro D V Λ K₀ hKo hK1
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI := (GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V).2.1
  let H : Subgroup (GA D V) := K₀.comap (finE V)
  have hHo : IsOpen (H : Set (GA D V)) := hKo
  obtain ⟨e0, he0⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  let jm : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram →* GA D V :=
    (e0.symm.toMulEquiv.toMonoidHom).comp (MonoidHom.inr _ _)
  have hj0 : ∀ k, e0 (jm k) = (1, k) := fun k => e0.apply_symm_apply _
  have hfin : ∀ h : GA D V, finE V (jm (e0 h).2) = finE V h := by
    intro h
    have h1 : finHom V (jm (e0 h).2) = finHom V h := by
      refine Units.ext ?_
      have a1 := (he0 (jm (e0 h).2)).1
      have a2 := (he0 h).1
      rw [hj0] at a1
      exact a1.symm.trans a2
    rw [finE_eq, finE_eq, h1]
  have hinf : ∀ k, jm k ∈ GfC V := by
    intro k
    have a1 := (he0 (jm k)).2
    rw [hj0] at a1
    exact Units.ext a1.symm
  have hmk : ∀ h : GA D V, DoubleCoset.mk (GQ V) H (jm (e0 h).2) = DoubleCoset.mk (GQ V) H h := by
    intro h
    refine (DoubleCoset.eq _ _ _ _).2 ⟨1, one_mem _, (jm (e0 h).2)⁻¹ * h, ?_, by group⟩
    show finE V ((jm (e0 h).2)⁻¹ * h) ∈ K₀
    rw [map_mul, map_inv, hfin, inv_mul_cancel]
    exact one_mem _
  let g : DoubleCoset.Quotient (GQ V : Set (GA D V)) (H : Set (GA D V)) → GA D V :=
    fun q => jm (e0 (Quotient.out q)).2
  have hgj : ∀ q, DoubleCoset.mk (GQ V) H (g q) = q := fun q => (hmk _).trans (Quotient.out_eq' q)
  have hJc : Countable (DoubleCoset.Quotient (GQ V : Set (GA D V)) (H : Set (GA D V))) := by
    obtain ⟨s, hs, hd⟩ := TopologicalSpace.exists_countable_dense (GA D V)
    haveI := hs.to_subtype
    have hsurj : Function.Surjective (fun x : s => DoubleCoset.mk (GQ V) H (x : GA D V)) := by
      intro q
      have hU : IsOpen ((fun x => Quotient.out q * x) '' (H : Set (GA D V))) := isOpenMap_mul_left _ _ hHo
      obtain ⟨x, hxs, ⟨k, hk, rfl⟩⟩ := hd.exists_mem_open hU ⟨_, 1, one_mem _, mul_one _⟩
      refine ⟨⟨_, hxs⟩, ?_⟩
      refine ((DoubleCoset.eq _ _ _ _).2 ⟨1, one_mem _, k⁻¹, inv_mem hk, by group⟩).trans (Quotient.out_eq' q)
    exact hsurj.countable
  refine ⟨_, hJc, g, fun j => hinf _, fun i j hE => ?_, fun h => ?_⟩
  · obtain ⟨γ, hγ, κ, hκ, he⟩ := hE
    obtain ⟨γ₀, hγ₀, hγf⟩ := GlobalTheory.RepsInj.gq_of_isUA D V γ hγ
    have hx : ((finHom V ((γ₀ * g i)⁻¹ * g j)).1 : Matrix (Fin V.rank) (Fin V.rank)
        (RA (maximalRealSubfield D.host.E) D.host.E)) = κ := by
      have h1 : ((finHom V (γ₀ * g i)).1 : Matrix (Fin V.rank) (Fin V.rank)
          (RA (maximalRealSubfield D.host.E) D.host.E)) * κ = (finHom V (g j)).1 := by
        rw [map_mul, Units.val_mul, hγf, he]
      rw [map_mul, map_inv, Units.val_mul, ← h1, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mul]
    have hxH : finE V ((γ₀ * g i)⁻¹ * g j) ∈ K₀ := by
      have h3 := isKM_one_of_three _ _ _ _ hκ
      rw [← hx] at h3
      exact hK1 _ h3
    have e : DoubleCoset.mk (GQ V) H (g i) = DoubleCoset.mk (GQ V) H (g j) :=
      (DoubleCoset.eq _ _ _ _).2 ⟨γ₀, hγ₀, (γ₀ * g i)⁻¹ * g j, hxH, by group⟩
    exact (hgj i).symm.trans (e.trans (hgj j))
  · obtain ⟨γ, hγ, k, hk, e⟩ := (DoubleCoset.eq _ _ _ _).1 (hgj (DoubleCoset.mk (GQ V) H h))
    refine ⟨DoubleCoset.mk (GQ V) H h, γ⁻¹, inv_mem hγ, ?_⟩
    generalize g (DoubleCoset.mk (GQ V) H h) = x at e ⊢
    subst e
    have e2 : x⁻¹ * γ⁻¹ * (γ * x * k) = k := by group
    rw [e2]
    exact hk

end GlobalTheory.CovTop.VolUp.Reps
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_countable_coset_representatives : ∀ (D : D7) (V : HSp D) (Λ : Set (Fin V.rank → D.host.E)) (K₀ : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))), IsOpen {h : GA D V | finE V h ∈ K₀} → (∀ h : GA D V, IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) Λ 1 ((finHom V h).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) → finE V h ∈ K₀) → ∃ (J : Type) (_ : Countable J) (g : J → GA D V), (∀ j, g j ∈ GfC V) ∧ (∀ i j, UEquiv (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) Λ 3 ((finHom V (g i)).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) ((finHom V (g j)).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) → i = j) ∧ ∀ h : GA D V, ∃ j, ∃ γ ∈ GQ V, finE V ((g j)⁻¹ * γ * h) ∈ K₀ := by
  atlas_forward_decl GlobalTheory.CovTop.VolUp.Reps.exists_reps
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.CovTop.VolUp.RatStab

set_option maxHeartbeats 1000000 in

theorem main : ∀ (D : D7) (V : HSp D) (Λ L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (g : GA D V) (δ : GL (Fin V.rank) D.host.E), (hat (maximalRealSubfield D.host.E) (L : Set (Fin V.rank → D.host.E)) : Set (Fin V.rank → RA (maximalRealSubfield D.host.E) D.host.E)) = ((finHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)).mulVec '' (hat (maximalRealSubfield D.host.E) (Λ : Set (Fin V.rank → D.host.E)) : Set (Fin V.rank → RA (maximalRealSubfield D.host.E) D.host.E)) → IsUStab (-(V.gram)ᵀ) L δ → ∃ γ ∈ GQ V, (∀ τ θ, IsInfEmb τ θ → infMat D.sp.cm.sig V.gram θ γ = (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ) ∧ IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (Λ : Set (Fin V.rank → D.host.E)) 1 ((finHom V (g⁻¹ * γ * g)).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) := by
  intro D V Λ L g δ hhat hδ
  have : IsTotallyReal D.host.F := D.sp.cm.totReal
  obtain ⟨γ₀, hQ, hfin, harch⟩ := GlobalTheory.RepConv.exists_rat V δ hδ.1
  refine ⟨γ₀, hQ, fun τ θ hθ => harch τ θ hθ, ?_⟩
  have hLδ : ∀ x ∈ L, ∃ y ∈ L, (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).mulVec x - x = (1 : ℕ) • y :=
    fun x hx => ⟨_, sub_mem ((hδ.2 x).1 hx) hx, by simp⟩
  have hLδi : ∀ x ∈ L, ∃ y ∈ L, ((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E).mulVec x - x = (1 : ℕ) • y := by
    intro x hx
    have hx' : ((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E).mulVec x ∈ L := by
      rw [hδ.2]
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      exact hx
    exact ⟨_, sub_mem hx' hx, by simp⟩
  have hf : (finHom V (g⁻¹ * γ₀ * g)).1 =
      ((finHom V g)⁻¹).1 * (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (Af D.host.F)) * (finHom V g).1 := by
    rw [← hfin]
    simp only [map_mul, map_inv, Units.val_mul]
  have hfi : (finHom V (g⁻¹ * γ₀⁻¹ * g)).1 =
      ((finHom V g)⁻¹).1 * ((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (Af D.host.F)) * (finHom V g).1 := by
    have hfin' : ((finHom V γ₀)⁻¹).1 = ((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (Af D.host.F)) := by
      apply Units.inv_eq_of_mul_eq_one_left
      rw [hfin, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    rw [← hfin']
    simp only [map_mul, map_inv, Units.val_mul]
  have c1 := GlobalTheory.RepConv.hat_cong_conj (F := D.host.F) (Λ : Set (Fin V.rank → D.host.E))
      (L : Set (Fin V.rank → D.host.E)) (finHom V g) hhat δ.1 1 hLδ
  have c2 := GlobalTheory.RepConv.hat_cong_conj (F := D.host.F) (Λ : Set (Fin V.rank → D.host.E))
      (L : Set (Fin V.rank → D.host.E)) (finHom V g) hhat (δ⁻¹ : GL (Fin V.rank) D.host.E).1 1 hLδi
  refine ⟨GlobalTheory.FinUA.isUA_finHom D V _, ?_, ?_⟩
  · intro x hx
    rw [hf]
    exact c1 x hx
  · intro x hx
    obtain ⟨y, hy, e⟩ := c2 x hx
    refine ⟨(finHom V (g⁻¹ * γ₀⁻¹ * g)).1 *ᵥ x, ?_, ?_⟩
    · rw [hfi]
      have : (((finHom V g)⁻¹).1 * ((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (Af D.host.F)) * (finHom V g).1) *ᵥ x = x + (1 : ℕ) • y := by
        rw [← e]; abel
      rw [this]; exact add_mem hx (by simpa using hy)
    · rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul]
      have : g⁻¹ * γ₀ * g * (g⁻¹ * γ₀⁻¹ * g) = 1 := by group
      rw [this, map_one, Units.val_one, Matrix.one_mulVec]

end GlobalTheory.CovTop.VolUp.RatStab
end

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_completion_image_finHom_mulVec : ∀ (D : D7) (V : HSp D) (Λ L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (g : GA D V) (δ : GL (Fin V.rank) D.host.E), (hat (maximalRealSubfield D.host.E) (L : Set (Fin V.rank → D.host.E)) : Set (Fin V.rank → RA (maximalRealSubfield D.host.E) D.host.E)) = ((finHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)).mulVec '' (hat (maximalRealSubfield D.host.E) (Λ : Set (Fin V.rank → D.host.E)) : Set (Fin V.rank → RA (maximalRealSubfield D.host.E) D.host.E)) → IsUStab (-(V.gram)ᵀ) L δ → ∃ γ ∈ GQ V, (∀ τ θ, IsInfEmb τ θ → infMat D.sp.cm.sig V.gram θ γ = (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ) ∧ IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (Λ : Set (Fin V.rank → D.host.E)) 1 ((finHom V (g⁻¹ * γ * g)).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) := by
  atlas_forward_decl GlobalTheory.CovTop.VolUp.RatStab.main
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolUp

theorem exists_measurableSet_reps_covolume : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Γ : Subgroup (GL (Fin r) E)) (ν : Measure (realSU Ψ G)) [ν.IsMulLeftInvariant], (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → (∀ γ ∈ Γ, IsUStab G Λ γ) → ∃ S : Set (realSU Ψ G), MeasurableSet S ∧ ν S = covolume (inReal Ψ G Γ) (realSU Ψ G) ν ∧ ∀ s : realSU Ψ G, ∃ δ ∈ Γ, ∃ hδ : embGL Ψ r δ ∈ realSU Ψ G, (⟨embGL Ψ r δ, hδ⟩ : realSU Ψ G) * s ∈ S := by
  intro E _ _ _ r Ψ G Λ Γ ν _ hΨ hfg hsp hΓ
  haveI := GlobalTheory.SUCount.discrete_inReal hΨ G Γ Λ hfg hsp (fun γ hγ x hx => ((hΓ γ hγ).2 x).1 hx)
  haveI := GlobalTheory.countable_of_discrete_subgroup (inReal Ψ G Γ)
  obtain ⟨D, hD, hu, hF⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (inReal Ψ G Γ)
  refine ⟨D, hD, ((hF ν).covolume_eq_volume).symm, fun s => ?_⟩
  obtain ⟨g, hg, -⟩ := hu s
  obtain ⟨δ, hδ, e⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 g.2)
  have hmem : embGL Ψ r δ ∈ realSU Ψ G := e ▸ g.1.2
  refine ⟨δ, hδ, hmem, ?_⟩
  have hg' : ((g : realSU Ψ G)) = ⟨embGL Ψ r δ, hmem⟩ := Subtype.ext e.symm
  rw [← hg']
  exact hg

end GlobalTheory.CovTop.VolUp
end

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fundamental_set_measure_realSU_stabilizer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Γ : Subgroup (GL (Fin r) E)) (ν : Measure (realSU Ψ G)) [ν.IsMulLeftInvariant], (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → (∀ γ ∈ Γ, IsUStab G Λ γ) → ∃ S : Set (realSU Ψ G), MeasurableSet S ∧ ν S = covolume (inReal Ψ G Γ) (realSU Ψ G) ν ∧ ∀ s : realSU Ψ G, ∃ δ ∈ Γ, ∃ hδ : embGL Ψ r δ ∈ realSU Ψ G, (⟨embGL Ψ r δ, hδ⟩ : realSU Ψ G) * s ∈ S := by
  atlas_forward_decl GlobalTheory.CovTop.VolUp.exists_measurableSet_reps_covolume
end

section
section
namespace GlobalTheory.CovTop.VolUp

set_option maxHeartbeats 2000000 in
theorem mass_bound_numbers_le_exp : ∀ (f r : ℕ) (L n g h rd P : ℝ), 2 ≤ f → 2 ≤ r → 1 ≤ L → (f : ℝ) * (r : ℝ) ^ 2 ≤ Real.exp L → 1 ≤ rd → Real.log rd ≤ 2 * L → 0 < n → Real.log n ≤ 2 * f * (r : ℝ) ^ 2 * Real.log g → Real.log g ≤ 30 * L → 0 < h → Real.log h ≤ f * Real.log rd + 2 * f * Real.log (1 + f * Real.log rd) → 0 ≤ P → P ≤ 2 ^ (r * (r - 1) / 2) * (2 * Real.pi) ^ (r - 1) * √r → n * (1000 * (f : ℝ) * (r : ℝ) ^ 3) ^ (f * r ^ 2) * (h * 3 ^ (2 * f) * ((3 : ℝ) ^ (2 * f * r ^ 2) * rd ^ ((f : ℝ) * ((r : ℝ) ^ 2 - 1) / 2) * P ^ f)) ≤ Real.exp (119 * (f * (r : ℝ) ^ 2 * L)) := by
  intro f r L n g h rd P hf hr hL hfr hrd hlrd hn hlogn hlogg hh hlogh hP0 hP
  have hf' : (2:ℝ) ≤ f := by exact_mod_cast hf
  have hr' : (2:ℝ) ≤ r := by exact_mod_cast hr
  have hf0 : (0:ℝ) ≤ f := by linarith
  have hr2 : (4:ℝ) ≤ (r:ℝ)^2 := by nlinarith
  have hfL : 0 ≤ (f:ℝ) * L := by positivity
  have hfr0 : 0 ≤ (f:ℝ) * (r:ℝ)^2 := by positivity
  have hU4 : 4 * ((f:ℝ) * L) ≤ (f:ℝ) * (r:ℝ)^2 * L := by nlinarith
  have hUfr : (f:ℝ) * (r:ℝ)^2 ≤ (f:ℝ) * (r:ℝ)^2 * L := by nlinarith
  have hUf : 4 * (f:ℝ) ≤ (f:ℝ) * (r:ℝ)^2 * L := by nlinarith
  set U : ℝ := (f:ℝ) * (r:ℝ)^2 * L with hU
  have hU0 : 0 ≤ U := by linarith
  have hlrd0 : 0 ≤ Real.log rd := Real.log_nonneg hrd
  have he2 : (3:ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2:ℝ)]
  have hexpL : 0 < Real.exp L := Real.exp_pos L

  have hA : n ≤ Real.exp (60 * U) := by
    rw [← Real.log_le_iff_le_exp hn]
    have : 2 * (f:ℝ) * (r:ℝ)^2 * Real.log g ≤ 2 * f * (r:ℝ)^2 * (30 * L) :=
      mul_le_mul_of_nonneg_left hlogg (by positivity)
    rw [hU]; linarith

  have he7 : (1000:ℝ) ≤ Real.exp 7 := by
    have h1 := Real.exp_one_gt_d9
    have : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc (1000:ℝ) ≤ 2.7182818283 ^ 7 := by norm_num
      _ ≤ Real.exp 1 ^ 7 := by gcongr
  have hB1 : 1000 * (f:ℝ) * (r:ℝ)^3 ≤ Real.exp (9 * L) := by
    have hfr3 : (f:ℝ) * (r:ℝ)^3 ≤ ((f:ℝ) * (r:ℝ)^2)^2 := by
      nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ f * r^3) (by nlinarith : (0:ℝ) ≤ f * r - 1)]
    have hsq : ((f:ℝ) * (r:ℝ)^2)^2 ≤ Real.exp L ^ 2 := by gcongr
    have h9 : Real.exp 7 * Real.exp L ^ 2 ≤ Real.exp (9 * L) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; apply Real.exp_le_exp.mpr; push_cast; linarith
    nlinarith [mul_le_mul he7 hsq (by positivity) (by positivity)]
  have hB : (1000 * (f:ℝ) * (r:ℝ)^3) ^ (f * r^2) ≤ Real.exp (9 * U) := by
    calc _ ≤ Real.exp (9 * L) ^ (f * r^2) := by gcongr
      _ = Real.exp (9 * U) := by rw [← Real.exp_nat_mul]; congr 1; rw [hU]; push_cast; ring

  have h4f : 4 * (f:ℝ) ≤ Real.exp L := by nlinarith
  have hflrd : (f:ℝ) * Real.log rd ≤ (f:ℝ) * (2 * L) := mul_le_mul_of_nonneg_left hlrd hf0
  have hlin : 1 + (f:ℝ) * Real.log rd ≤ Real.exp (2 * L) := by
    have h1 := Real.add_one_le_exp L
    have : Real.exp (2 * L) = Real.exp L * Real.exp L := by rw [← Real.exp_add]; ring_nf
    rw [this]
    have : 4 * (f:ℝ) * (L + 1) ≤ Real.exp L * Real.exp L := mul_le_mul h4f h1 (by linarith) hexpL.le
    nlinarith
  have hC : h ≤ Real.exp (2 * U) := by
    rw [← Real.log_le_iff_le_exp hh]
    have hl1 : Real.log (1 + (f:ℝ) * Real.log rd) ≤ 2 * L := by
      rw [Real.log_le_iff_le_exp (by positivity)]; exact hlin
    have : 2 * (f:ℝ) * Real.log (1 + f * Real.log rd) ≤ 2 * f * (2 * L) :=
      mul_le_mul_of_nonneg_left hl1 (by positivity)
    linarith

  have hD : (3:ℝ) ^ (2 * f) ≤ Real.exp U := by
    calc (3:ℝ) ^ (2 * f) ≤ Real.exp 2 ^ (2 * f) := by gcongr
      _ = Real.exp (4 * f) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
      _ ≤ Real.exp U := Real.exp_le_exp.mpr (by linarith)

  have hE : (3:ℝ) ^ (2 * f * r ^ 2) ≤ Real.exp (4 * U) := by
    calc (3:ℝ) ^ (2 * f * r ^ 2) ≤ Real.exp 2 ^ (2 * f * r ^ 2) := by gcongr
      _ = Real.exp (4 * ((f:ℝ) * (r:ℝ)^2)) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
      _ ≤ Real.exp (4 * U) := Real.exp_le_exp.mpr (by linarith)

  have hy0 : 0 ≤ (f:ℝ) * ((r:ℝ)^2 - 1) / 2 := by
    have : 0 ≤ (r:ℝ)^2 - 1 := by linarith
    positivity
  have hF : rd ^ ((f:ℝ) * ((r:ℝ)^2 - 1) / 2) ≤ Real.exp U := by
    rw [Real.rpow_def_of_pos (by linarith)]
    apply Real.exp_le_exp.mpr
    have : Real.log rd * ((f:ℝ) * ((r:ℝ)^2 - 1) / 2) ≤ 2 * L * ((f:ℝ) * ((r:ℝ)^2 - 1) / 2) :=
      mul_le_mul_of_nonneg_right hlrd hy0
    linarith

  have hP1 : P ≤ Real.exp (3 * (r:ℝ)^2) := by
    have h2 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
    have hpi : 2 * Real.pi ≤ Real.exp 2 := by
      have := Real.pi_lt_d2
      have h1 := Real.exp_one_gt_d9
      have he : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      have h3 : (2.7182818283:ℝ) ^ 2 ≤ Real.exp 1 ^ 2 := by gcongr
      have h4 : (6.3:ℝ) ≤ 2.7182818283 ^ 2 := by norm_num
      rw [he]; linarith
    have hA1 : (2:ℝ) ^ (r * (r - 1) / 2) ≤ Real.exp ((r:ℝ)^2) := by
      calc (2:ℝ) ^ (r * (r - 1) / 2) ≤ Real.exp 1 ^ (r * (r - 1) / 2) := by gcongr
        _ ≤ Real.exp 1 ^ (r ^ 2) := by
            apply pow_le_pow_right₀ (by linarith)
            calc r * (r - 1) / 2 ≤ r * (r - 1) := Nat.div_le_self _ _
              _ ≤ r * r := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
              _ = r ^ 2 := (sq r).symm
        _ = Real.exp ((r:ℝ)^2) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
    have hA2 : (2 * Real.pi) ^ (r - 1) ≤ Real.exp (2 * r) := by
      calc (2 * Real.pi) ^ (r - 1) ≤ Real.exp 2 ^ (r - 1) := by gcongr
        _ ≤ Real.exp 2 ^ r := pow_le_pow_right₀ (Real.one_le_exp (by norm_num)) (Nat.sub_le _ _)
        _ = Real.exp (2 * r) := by rw [← Real.exp_nat_mul]; ring_nf
    have hA3 : √(r:ℝ) ≤ Real.exp r := by
      have h1 := Real.add_one_le_exp (r:ℝ)
      calc √(r:ℝ) ≤ √((Real.exp r)^2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = Real.exp r := Real.sqrt_sq (Real.exp_pos _).le
    calc P ≤ _ := hP
      _ ≤ Real.exp ((r:ℝ)^2) * Real.exp (2 * r) * Real.exp r := by gcongr
      _ = Real.exp ((r:ℝ)^2 + 2 * r + r) := by rw [Real.exp_add, Real.exp_add]
      _ ≤ Real.exp (3 * (r:ℝ)^2) := Real.exp_le_exp.mpr (by nlinarith)
  have hG : P ^ f ≤ Real.exp (3 * U) := by
    calc P ^ f ≤ Real.exp (3 * (r:ℝ)^2) ^ f := pow_le_pow_left₀ hP0 hP1 f
      _ = Real.exp (f * (3 * (r:ℝ)^2)) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (3 * U) := Real.exp_le_exp.mpr (by linarith)

  have hEFG : (3:ℝ) ^ (2 * f * r ^ 2) * rd ^ ((f:ℝ) * ((r:ℝ)^2 - 1) / 2) * P ^ f
      ≤ Real.exp (4 * U) * Real.exp U * Real.exp (3 * U) :=
    mul_le_mul (mul_le_mul hE hF (Real.rpow_nonneg (by linarith) _) (Real.exp_pos _).le) hG
      (pow_nonneg hP0 _) (by positivity)
  have hCD : h * (3:ℝ) ^ (2 * f) ≤ Real.exp (2 * U) * Real.exp U :=
    mul_le_mul hC hD (by positivity) (Real.exp_pos _).le
  have hCG := mul_le_mul hCD hEFG
    (mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _)) (pow_nonneg hP0 _))
    (by positivity)
  have hAB : n * (1000 * (f:ℝ) * (r:ℝ)^3) ^ (f * r^2) ≤ Real.exp (60 * U) * Real.exp (9 * U) :=
    mul_le_mul hA hB (by positivity) (Real.exp_pos _).le
  have hall := mul_le_mul hAB hCG
    (mul_nonneg (mul_nonneg hh.le (by positivity))
      (mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _)) (pow_nonneg hP0 _)))
    (by positivity)
  refine hall.trans ?_
  simp only [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

end GlobalTheory.CovTop.VolUp
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.explicit_height_bound_log_discriminant : ∀ (f r : ℕ) (L n g h rd P : ℝ), 2 ≤ f → 2 ≤ r → 1 ≤ L → (f : ℝ) * (r : ℝ) ^ 2 ≤ Real.exp L → 1 ≤ rd → Real.log rd ≤ 2 * L → 0 < n → Real.log n ≤ 2 * f * (r : ℝ) ^ 2 * Real.log g → Real.log g ≤ 30 * L → 0 < h → Real.log h ≤ f * Real.log rd + 2 * f * Real.log (1 + f * Real.log rd) → 0 ≤ P → P ≤ 2 ^ (r * (r - 1) / 2) * (2 * Real.pi) ^ (r - 1) * √r → n * (1000 * (f : ℝ) * (r : ℝ) ^ 3) ^ (f * r ^ 2) * (h * 3 ^ (2 * f) * ((3 : ℝ) ^ (2 * f * r ^ 2) * rd ^ ((f : ℝ) * ((r : ℝ) ^ 2 - 1) / 2) * P ^ f)) ≤ Real.exp (119 * (f * (r : ℝ) ^ 2 * L)) := by
  atlas_forward_decl GlobalTheory.CovTop.VolUp.mass_bound_numbers_le_exp
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolUp

theorem measure_le_tsum_of_cover {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulLeftInvariant] (Γ : Subgroup G) [Countable Γ] {𝓕 : Set G} (h : IsFundamentalDomain Γ 𝓕 μ) {J : Type} [Countable J]
    (S : J → Set G) (hS : ∀ j, MeasurableSet (S j)) (hc : ∀ x, ∃ j, ∃ γ ∈ Γ, γ * x ∈ S j) : μ 𝓕 ≤ ∑' j, μ (S j) := by
  refine le_trans ?_ (measure_iUnion_le S)
  rw [h.measure_eq_tsum (⋃ j, S j)]
  refine le_trans (measure_mono ?_) (measure_iUnion_le _)
  intro x hx
  obtain ⟨j, γ, hγ, hj⟩ := hc x
  refine Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : Γ)⁻¹, ?_, hx⟩
  rw [Set.mem_inv_smul_set_iff]
  exact Set.mem_iUnion.2 ⟨j, hj⟩

noncomputable def torBd (E : Type) [Field E] [NumberField E] (r : ℕ) : ℝ :=
  (classNumber E : ℝ) * 3 ^ (2 * fdeg E) * ((3 : ℝ) ^ (2 * fdeg E * r ^ 2) * rdE E ^ ((fdeg E : ℝ) * ((r : ℝ) ^ 2 - 1) / 2) *
    (Real.sqrt r * ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ fdeg E)

theorem sum_covolume_le_torBd (hT : GlobalTheory.Published.TamagawaSpecialUnitary) (E : Type) [Field E] [NumberField E] [IsCMField E]
    (r m : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (X : Fin m → Data E r)
    (g : Fin m → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) (x0 : ∀ i, Frame (X i).Ψ r)
    (hr : 2 ≤ r) (hU : Unr E) (hSD : SelfDualLat G Λ)
    (hUA : ∀ i, IsUA (IsCMField.complexConj E) G (g i))
    (hdist : ∀ i j, UEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) 3 (g i) (g j) → i = j)
    (hX : ∀ i, (X i).Gm = G ∧ (X i).Ψ = Ψ ∧
      ((X i).Λ : Set (Fin r → E)) = latOf (maximalRealSubfield E) (g i) (Λ : Set (Fin r → E)) ∧
      (∀ γ, γ ∈ (X i).Γ ↔ IsUStab G (X i).Λ γ ∧
        ∀ x ∈ (X i).Λ, ∃ y ∈ (X i).Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = 3 • y) ∧ IsOrth (X i) (x0 i)) :
    ∑ i, covolume (inReal (X i).Ψ (X i).Gm (X i).Γ) (realSU (X i).Ψ (X i).Gm) (riemHaar (X i).Ψ (X i).Gm (x0 i)) ≤
      ENNReal.ofReal (torBd E r) := by
  classical
  have htor := GlobalTheory.UCls.torusBound E r 3 G Λ (by omega) (by omega) hU hSD
  set h : ℕ := classNumber E * 3 ^ (2 * fdeg E) with hh
  set K : ℝ := ((3 : ℕ) : ℝ) ^ (2 * fdeg E * r ^ 2) * rdE E ^ ((fdeg E : ℝ) * ((r : ℝ) ^ 2 - 1) / 2) *
    (Real.sqrt r * ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ fdeg E with hK
  let cv : Fin m → ℝ≥0∞ := fun i => covolume (inReal (X i).Ψ (X i).Gm (X i).Γ) (realSU (X i).Ψ (X i).Gm)
    (riemHaar (X i).Ψ (X i).Gm (x0 i))
  have hTA : ∀ i, IsTA (IsCMField.complexConj E) (g i).det := fun i => GlobalTheory.unitary_det_isTA E r G (g i) hSD.2.1 (hUA i)
  let f : Fin m → Quot fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} =>
      TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) 3 a.1 b.1 := fun i => Quot.mk _ ⟨(g i).det, hTA i⟩
  have hQfin : Finite (Quot fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} =>
      TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) 3 a.1 b.1) := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    have h1 : torusNo (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) 3 = ⊤ := ENat.card_eq_top_of_infinite
    rw [h1] at htor
    exact absurd htor (by simp)
  have hcard : (Finset.univ.image f).card ≤ h := by
    have h1 : (Finset.univ.image f).card ≤ Nat.card (Quot fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} =>
        TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) 3 a.1 b.1) := by
      haveI := Fintype.ofFinite (Quot fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} =>
        TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) 3 a.1 b.1)
      rw [Nat.card_eq_fintype_card]; exact Finset.card_le_univ _
    have h2 : ((Nat.card (Quot fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} =>
        TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) 3 a.1 b.1) : ℕ) : ℕ∞) ≤ h := by
      rw [← ENat.card_eq_coe_natCard]; exact htor
    exact h1.trans (by exact_mod_cast h2)
  have hfib : ∀ q ∈ Finset.univ.image f, ∑ i ∈ Finset.univ.filter (fun i => f i = q), cv i ≤ ENNReal.ofReal K := by
    intro q hq
    obtain ⟨i0, -, hi0⟩ := Finset.mem_image.1 hq
    refine GlobalTheory.T.unitary_frames_strong_approximation hT E r 3 m G Λ Ψ X g x0 _ (g i0) hr le_rfl hU hSD (hUA i0) hUA ?_ (fun i _ j _ => hdist i j)
      (fun i _ => hX i)
    intro i hi
    have hfi : f i0 = f i := by rw [hi0, (Finset.mem_filter.1 hi).2]
    exact GlobalTheory.UCls.torus_eqvGen_main E r 3 G (Λ : Set (Fin r → E)) ⟨(g i0).det, hTA i0⟩ ⟨(g i).det, hTA i⟩ (Quot.eqvGen_exact hfi)
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image f) (g := f)
    (fun i _ => Finset.mem_image_of_mem f (Finset.mem_univ i))]
  calc _ ≤ ∑ q ∈ Finset.univ.image f, ENNReal.ofReal K := Finset.sum_le_sum hfib
    _ = ((Finset.univ.image f).card : ℝ≥0∞) * ENNReal.ofReal K := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (h : ℝ≥0∞) * ENNReal.ofReal K := by gcongr
    _ = ENNReal.ofReal (h * K) := by rw [ENNReal.ofReal_mul (p := (h : ℝ)) (by positivity), ENNReal.ofReal_natCast]
    _ = _ := by rw [hh, hK, torBd]; push_cast; rfl

theorem exists_frame_transport {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (p0 : ℕ) (x : Frame Ψ r) (h1 : X.Ψ = Ψ) (h2 : X.Gm = G)
    (h3 : X.p0 = p0)
    (hx : ∀ τ : Ψ, ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 G (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) :
    ∃ x' : Frame X.Ψ r, IsOrth X x' ∧ covolume (inReal Ψ G X.Γ) (realSU Ψ G) (riemHaar Ψ G x) =
      covolume (inReal X.Ψ X.Gm X.Γ) (realSU X.Ψ X.Gm) (riemHaar X.Ψ X.Gm x') := by
  subst h1 h2 h3
  exact ⟨x, hx, rfl⟩

set_option maxHeartbeats 1000000 in

theorem mass_le (hT : GlobalTheory.Published.TamagawaSpecialUnitary) (D : D7) (V : HSp D) (hV : V.SigOK) (P Q : ℕ)
    (hsig : ∀ τ, V.sig τ = (P, Q)) (r : ℕ) (hrk : V.rank = r) (hr : 2 ≤ r) (hU : Unr D.host.E)
    (K K₀ : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))) (hle : K ≤ K₀) (hn : K.relIndex K₀ ≠ 0)
    (hKo : IsOpen {h : GA D V | finE V h ∈ K}) (hK₀o : IsOpen {h : GA D V | finE V h ∈ K₀})
    (hK₀ : ∀ h : GA D V, IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) 1
      ((finHom V h).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) → finE V h ∈ K₀)
    (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (hF : IsMeasFD V K μ 𝓕) :
    μ 𝓕 ≤ (K.relIndex K₀ : ℝ≥0∞) *
      ENNReal.ofReal ((1000 * (D.R.f : ℝ) * (r : ℝ) ^ 3) ^ (D.R.f * r ^ 2)) * ENNReal.ofReal (torBd D.host.E r) := by
  classical
  subst hrk
  obtain ⟨-, -, hB, hC⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI := hF.1.1
  obtain ⟨⟨θ, hθ⟩, H1⟩ := hF.1.2
  obtain ⟨⟨A, hA⟩, H2⟩ := H1 θ hθ
  obtain ⟨⟨m, hm⟩, -⟩ := H2 A hA
  obtain ⟨X₀, σ, x, e, hG, hσ, hx, hid⟩ := GlobalTheory.T.exists_flagDomain_orthonormalFrame_identification D V P Q hV hsig A hA
  have hcard : X₀.Ψ.card = D.R.f := by
    rw [← Fintype.card_coe, ← Fintype.card_congr σ, D.what₂.card_Tau]
  have hf : 1 ≤ X₀.Ψ.card := by rw [hcard]; unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
  obtain ⟨rp, hrpc, hrp⟩ := GlobalTheory.T.exists_continuous_realComponentHom_unitaryAdelic D V θ A hV hθ hA
  let a₀ : ∀ ρ : D.what₂.Tau, Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2 := fun ρ => (e ρ).symm ⟨0, by omega⟩
  obtain ⟨π, hπc, hπ, hπe⟩ := GlobalTheory.T.exists_continuous_equivariant_detOneFactorProjection D.host.E V.rank D.what₂.Tau _ _ X₀.Ψ X₀.Gm x σ A e a₀ hid
  have hreal := GlobalTheory.T.unitary_group_measure_decomposition D.host.E V.rank D.what₂.Tau _ _ X₀.Ψ X₀.Gm x σ A e a₀ π m (by omega) hf hid hπc hπ hπe hm
  rw [hcard] at hreal
  obtain ⟨J, hJ, g, hg, hdist, hcov⟩ := GlobalTheory.T.exists_countable_coset_representatives D V (GlobalTheory.Member.latC V) K₀ hK₀o hK₀
  have hSD := GlobalTheory.Member.selfDualLat_neg_gram_transpose D V
  have hUA := fun j => GlobalTheory.FinUA.isUA_finHom D V (g j)
  choose L hL hLhat hLsd using fun j => GlobalTheory.UCls.selfDual_latOf_translate D.host.E V.rank _ _ _ hSD (hUA j)
  choose X hXG hXΨ hXp hXΛ hXΓ using fun j =>
    GlobalTheory.PrincData.exists_princ_data D.host.E V.rank 3 X₀ (L j) le_rfl (hLsd j).2.2.1 (hLsd j).2.2.2.1
  haveI : (riemHaar X₀.Ψ X₀.Gm x).IsMulLeftInvariant := by unfold riemHaar; infer_instance
  choose S hSm hSv hSc using fun j => GlobalTheory.T.exists_fundamental_set_measure_realSU_stabilizer D.host.E V.rank X₀.Ψ X₀.Gm (L j) (X j).Γ (riemHaar X₀.Ψ X₀.Gm x) X₀.cmType
    (hLsd j).2.2.1 (hLsd j).2.2.2.1 (fun γ hγ => ((hXΓ j γ).1 hγ).1)
  choose y hy hyv using fun j => exists_frame_transport (X j) X₀.Ψ X₀.Gm X₀.p0 x (hXΨ j) (hXG j) (hXp j) hx
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  have hBm : ∀ j, MeasurableSet (π ⁻¹' S j) := fun j => hπc.measurable (hSm j)
  let T : J → Set (GA D V) := fun j => {h | finE V ((g j)⁻¹ * h) ∈ K₀ ∧ rp h ∈ π ⁻¹' S j}
  have hTm : ∀ j, MeasurableSet (T j) := fun j =>
    ((hK₀o.preimage (continuous_const.mul continuous_id)).measurableSet).inter (hrpc.measurable (hBm j))
  have hTc : ∀ h, ∃ j, ∃ γ ∈ GQ V, γ * h ∈ T j := by
    intro h
    obtain ⟨j, γ, hγ, hk⟩ := hcov h
    obtain ⟨δ, hδ, hδs, hδS⟩ := hSc j (π (rp (γ * h)))
    obtain ⟨γ', hγ', hinf, hKM⟩ := GlobalTheory.T.lattice_completion_image_finHom_mulVec D V (GlobalTheory.Member.latC V) (L j) (g j) δ (hLhat j) (hG ▸ ((hXΓ j δ).1 hδ).1)
    refine ⟨j, γ' * γ, (GQ V).mul_mem hγ' hγ, ?_, ?_⟩
    · have := K₀.mul_mem (hK₀ _ hKM) hk
      rw [← map_mul] at this
      convert this using 2
      group
    · change π (rp (γ' * γ * h)) ∈ S j
      rw [mul_assoc, map_mul, hπe ⟨embGL X₀.Ψ V.rank δ, hδs⟩ (rp γ') fun ρ => ?_]
      · exact hδS
      · rw [hrp γ' ρ, hinf (σ ρ).1 _ ((hσ ρ).symm ▸ hθ ρ)]
        rfl
  set C := ENNReal.ofReal ((1000 * (D.R.f : ℝ) * (V.rank : ℝ) ^ 3) ^ (D.R.f * V.rank ^ 2)) with hC'
  have hTle : ∀ j, μ (T j) ≤ (K.relIndex K₀ : ℝ≥0∞) * C *
      covolume (inReal (X j).Ψ (X j).Gm (X j).Γ) (realSU (X j).Ψ (X j).Gm) (riemHaar (X j).Ψ (X j).Gm (y j)) := by
    intro j
    refine (GlobalTheory.T.measure_translateLevel_realBox_le_index_mul D V θ A m rp K K₀ μ hV hθ hA hm hrpc hrp hle hn hKo hF.1 (g j) (hg j) _ (hBm j)).trans ?_
    rw [mul_assoc, ← hyv j, ← hSv j]
    gcongr
    exact hreal _ (hSm j)
  refine (measure_le_tsum_of_cover μ (GQ V) hF.2 T hTm hTc).trans ((ENNReal.tsum_le_tsum hTle).trans ?_)
  rw [ENNReal.tsum_mul_left]
  gcongr
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  rw [← Finset.sum_coe_sort s, ← s.equivFin.symm.sum_comp]
  exact sum_covolume_le_torBd hT D.host.E V.rank s.card _ (GlobalTheory.Member.latC V) X₀.Ψ (fun i => X (s.equivFin.symm i))
    (fun i => (finHom V (g (s.equivFin.symm i))).1) (fun i => y (s.equivFin.symm i)) hr hU hSD (fun i => hUA _)
    (fun i j h => s.equivFin.symm.injective (Subtype.ext (hdist _ _ h)))
    (fun i => ⟨(hXG _).trans hG, hXΨ _, by rw [hXΛ]; exact hL _, fun γ => by rw [hXΛ, hXΓ, hG], hy _⟩)

end GlobalTheory.CovTop.VolUp

namespace GlobalTheory.CovTop.VolUp

open Formalism.IndefR.Links in

theorem log_mass_le (hP : GlobalTheory.CovTop.Hypotheses2) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m)
    (P : Formalism.L2.DIV.LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i)))
    (hF : IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) μ 𝓕) (L : ℝ) (hL : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.Sizes D L) :
    Real.log (μ 𝓕).toReal ≤ D.R.f * (D.R.r : ℝ) ^ 2 * Real.log ((D.R.r : ℝ) + 3) + (38 + 81) * (D.R.f * (D.R.r : ℝ) ^ 2 * L) := by
  obtain ⟨hn, hnl⟩ := GlobalTheory.T.level_index_bound_of_classicalTheorems hP D Tu C t0 hC i P
  have hrk : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hr : 2 ≤ D.R.r := Formalism.L2.Geo.two_le_r D
  have hm := mass_le hP.p6 D (Wc D i) (D.sp.W_sig _) _ _ (D.sp.W_sigval _ (Nat.le_add_left _ _) i.2) _ hrk hr
    (GlobalTheory.InertOfConj.unram D) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i (Formalism.L2.DIV.LevelP.full _ _ _))
    (fun k hk => ⟨hk.1, Subgroup.mem_top _⟩) hn (GlobalTheory.ParahoricCompact.isOpen_comap_lev _ _ _)
    (GlobalTheory.ParahoricCompact.isOpen_comap_lev _ _ _)
    (GlobalTheory.T.finitePart_mem_fullLevel_of_keeps_selfDualLattice D (Wc D i) (C.βW i) (C.ΛW i) _ (hC.βW i) hrk.le rfl) μ 𝓕 hF
  set n := (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P).relIndex (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i (Formalism.L2.DIV.LevelP.full _ _ _)) with hndef
  have hfin : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [show Module.finrank ℚ D.host.E = 4 * D.R.ord from D.host.finrank_cmField]
    unfold Ranks.f Ranks.n; ring
  have hfd : fdeg D.host.E = D.R.f := by unfold fdeg; omega
  have hf : 2 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
  have hnV : D.R.r ≤ D.R.nV := Nat.le_add_right _ _
  obtain ⟨h1, -, h3, h4⟩ := hL
  have hfR : (2 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hrR : (2 : ℝ) ≤ D.R.r := by exact_mod_cast hr
  have hnR : (D.R.r : ℝ) ≤ D.R.nV := by exact_mod_cast hnV
  have hfr : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 ≤ Real.exp L := by
    refine le_trans ?_ h1
    rw [sq, ← mul_assoc]; gcongr
  have hL1 : 1 ≤ L := by
    have : Real.exp 1 ≤ Real.exp L := by
      have := Real.exp_one_lt_d9
      nlinarith
    exact Real.exp_le_exp.1 this
  have hd1 : (1 : ℝ) ≤ |(discr D.host.E : ℝ)| := by
    have := Int.one_le_abs (discr_ne_zero D.host.E)
    exact_mod_cast this
  have hrd1 : 1 ≤ rdE D.host.E := Real.one_le_rpow hd1 (by positivity)
  have hlog : Real.log (rdE D.host.E) = Real.log |(discr D.host.E : ℝ)| / (2 * D.R.f) := by
    unfold rdE dE
    rw [Real.log_rpow (by linarith), hfin]; push_cast; ring
  have hh := GlobalTheory.log_classNumber_le_log_abs_discr_div D.host.E D.R.f hfin
  rw [← hlog] at hh
  have hrdL : Real.log (rdE D.host.E) ≤ 2 * L := by
    have : rdE D.host.E = D.host.rdE := rfl
    rw [this]; linarith [abs_nonneg (dlogL D 1)]
  have hP0 : 0 ≤ Real.sqrt D.R.r * ∏ i ∈ Finset.Icc 2 D.R.r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i :=
    mul_nonneg (Real.sqrt_nonneg _) (Finset.prod_nonneg fun i _ => tsum_nonneg fun n => by positivity)
  have ha := GlobalTheory.T.explicit_height_bound_log_discriminant D.R.f D.R.r L n _ (classNumber D.host.E) (rdE D.host.E) _ hf hr hL1 hfr hrd1 hrdL
    (by exact_mod_cast Nat.pos_of_ne_zero hn) hnl h3 (by exact_mod_cast classNumber_pos D.host.E) hh hP0
    (GlobalTheory.volumeConstant_le D.R.r hr)
  have hle : (μ 𝓕).toReal ≤ Real.exp (119 * (D.R.f * (D.R.r : ℝ) ^ 2 * L)) := by
    refine ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le (hm.trans ?_)
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold torBd
    rw [hfd]
    exact ha
  have h0 : 0 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * Real.log ((D.R.r : ℝ) + 3) :=
    mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  have h5 : Real.log (μ 𝓕).toReal ≤ 119 * (D.R.f * (D.R.r : ℝ) ^ 2 * L) := by
    rcases (ENNReal.toReal_nonneg (a := μ 𝓕)).eq_or_lt with h | h
    · rw [← h, Real.log_zero]; positivity
    · exact (Real.log_le_iff_le_exp h).2 hle
  linarith

end GlobalTheory.CovTop.VolUp
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_fundamental_domain_volume_le : ∀ (hP : Hypotheses2) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) (hF : IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) μ 𝓕) (L : ℝ) (hL : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.Sizes D L), Real.log (μ 𝓕).toReal ≤ D.R.f * (D.R.r : ℝ) ^ 2 * Real.log ((D.R.r : ℝ) + 3) + (38 + 81) * (D.R.f * (D.R.r : ℝ) ^ 2 * L) := by
  atlas_forward_decl GlobalTheory.CovTop.VolUp.log_mass_le
end
