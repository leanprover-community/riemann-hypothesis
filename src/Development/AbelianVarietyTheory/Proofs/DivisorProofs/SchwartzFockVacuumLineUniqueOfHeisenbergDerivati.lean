import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasArchDerivativeOnPureTensorUniqueAdelicOperatoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiTensorSumFockHeisenbergISmulSignConjVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTracePairingBilinearNondegenerateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzComplexStructureVacuumSolutionEqSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumEquationsInArchimedeanDarbouxCoordinat

section
open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.piTensorSumFockHeisenberg_I_smul_signConj_vacuum : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ} (c : ι → Matrix (Ix P Q) (Ix R S) ℂ),
    sumPl (V := fun _ : ι => Pol P Q R S) (fun w => heisOp (Complex.I • (Jm P Q * c w * Jm R S)))
      (PiTensorProduct.tprod ℂ fun _ => 1) =
    Complex.I • sumPl (V := fun _ : ι => Pol P Q R S) (fun w => heisOp (c w)) (PiTensorProduct.tprod ℂ fun _ => 1) := by
  first | exact @GlobalTheory.FockVac.sumPl_heisOp_vacuum | exact GlobalTheory.FockVac.sumPl_heisOp_vacuum | (intros; apply GlobalTheory.FockVac.sumPl_heisOp_vacuum <;> assumption)
end

section
open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVacuumEquations_in_archimedeanDarbouxCoordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (ε : InfinitePlace F → ℤˣ), IsCMExt F E σ → Framed τ JA JB a b A C →
    ∃ (J e : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
        ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))
      (e' : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F)),
      (∀ y, J (J y) = -y) ∧ (∀ y, e (e y) = e y) ∧ (∀ y, J (e y) = e (J y)) ∧ (∀ y, (e y).1 = e' y.1) ∧
      (∀ y x, trPair F κ x (e y).2 = trPair F κ (e' x) y.2) ∧
      ∀ y, ∃ (u u' u₁ : Matrix α β (AE F E)) (c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ),
        At (evI F) u ∧ At (evI F) u' ∧ At (evI F) u₁ ∧ (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) ∧
        (∀ w, u'.map (piInf (τ w)) = A w * ((((ε w : ℤ) : ℂ) * Complex.I) • (Jm P Q * c w * Jm R S)) * (C w)ᵀ) ∧
        (∀ w, u₁.map (piInf (τ w)) = A w * (Complex.I • (Jm P Q * c w * Jm R S)) * (C w)ᵀ) ∧
        coord d u = y ∧ coord d u' = J (y - (2 : ℝ) • e y) ∧ coord d u₁ = J y := by
  first | exact @GlobalTheory.VacBridge.exists_bridge | exact GlobalTheory.VacBridge.exists_bridge | (intros; apply GlobalTheory.VacBridge.exists_bridge <;> assumption)
end

section
noncomputable section

open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.VacLn
theorem vac_ne_zero {ι : Type} [Fintype ι] {P Q R S : ℕ} :
    (PiTensorProduct.tprod ℂ fun _ : ι => (1 : Pol P Q R S)) ≠ 0 := by
  intro h
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap
    fun _ => (MvPolynomial.aeval (R := ℂ) (S₁ := ℂ) (σ := Ln P Q R S) fun _ => 0).toLinearMap)) h
  simp at this

theorem vacLine_of_derEx (hD : DerEx) : VacLine := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ hCM hStd hFr hΦ f₀ ε hyp
  obtain ⟨D, hDu⟩ := hD F E σ α β κ ψ JA JB d hStd
  obtain ⟨J, e, e', hJ, he, hJe, he1, he2, hy⟩ := GlobalTheory.T.fockVacuumEquations_in_archimedeanDarbouxCoordinates F E σ α β κ P Q R S τ JA JB d a b A C ε hCM hFr
  have hDx : ∀ u, At (evI F) u → ∀ (f : SInf F κ) x, D u f x = fderiv ℝ f x (coord d u).1 -
      2 * Real.pi * Complex.I * (trPair F κ x (coord d u).2 : ℝ) * f x := fun u hu f x => (hDu u hu f).2 x
  have hf : ∀ y x, fderiv ℝ f₀ x (J (y - (2 : ℝ) • e y)).1 - 2 * Real.pi * Complex.I *
      (trPair F κ x (J (y - (2 : ℝ) • e y)).2 : ℝ) * f₀ x =
      Complex.I * (fderiv ℝ f₀ x y.1 - 2 * Real.pi * Complex.I * (trPair F κ x y.2 : ℝ) * f₀ x) := by
    intro y x
    obtain ⟨u, u', u₁, c, hu, hu', -, hc, hc', -, h0, h', -⟩ := hy y
    have key := hyp u u' hu hu' c hc hc' (D u f₀) (D u' f₀) (hDu u hu f₀).1 (hDu u' hu' f₀).1
    have := congrArg (fun g : SInf F κ => g x) key
    simp only [SchwartzMap.smul_apply, smul_eq_mul] at this
    rw [hDx u hu, hDx u' hu', h0, h'] at this
    exact this
  set g₀ := Φ (PiTensorProduct.tprod ℂ fun _ => 1) with hg₀
  have hg0 : g₀ ≠ 0 := fun h => vac_ne_zero (hΦ.1 (h.trans (map_zero Φ).symm))
  have hg : ∀ y x, fderiv ℝ g₀ x (J y).1 - 2 * Real.pi * Complex.I * (trPair F κ x (J y).2 : ℝ) * g₀ x =
      Complex.I * (fderiv ℝ g₀ x y.1 - 2 * Real.pi * Complex.I * (trPair F κ x y.2 : ℝ) * g₀ x) := by
    intro y x
    obtain ⟨u, -, u₁, c, hu, -, hu₁, hc, -, hc₁, h0, -, h1⟩ := hy y
    have e0 := GlobalTheory.T.hasArchDerivativeOnPureTensor_unique_adelicOperators (hDu u hu g₀).1 (hΦ.2 u hu c hc _)
    have e1 := GlobalTheory.T.hasArchDerivativeOnPureTensor_unique_adelicOperators (hDu u₁ hu₁ g₀).1 (hΦ.2 u₁ hu₁ _ hc₁ _)
    rw [GlobalTheory.T.piTensorSumFockHeisenberg_I_smul_signConj_vacuum, map_smul, ← e0] at e1
    have := congrArg (fun g : SInf F κ => g x) e1
    simp only [SchwartzMap.smul_apply, smul_eq_mul] at this
    rw [hDx u hu, hDx u₁ hu₁, h0, h1] at this
    exact this
  obtain ⟨z, hz⟩ := GlobalTheory.T.schwartz_complexStructure_vacuum_solution_eq_smul (trPair F κ) (fun y h => GlobalTheory.T.archimedeanTracePairingBilinear_nondegenerate y h) J e e' hJ he hJe he1 he2 f₀ g₀ hg0 hg hf
  exact ⟨z, hz⟩

end GlobalTheory.VacLn
end
end
