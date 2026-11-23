module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst
public import Mathlib.RingTheory.PiTensorProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTracePairingBilinearNondegenerateStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanPhaseSpaceComplexStructureSignaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumPiTensorHeisenbergFactorwiseSignatureStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasArchDerivativeOnPureTensorUniqueAdelicOperatoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzComplexStructureVacuumSolutionEqSmulStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD GlobalTheory.VacLn

namespace GlobalTheory.HoweD

theorem vacD_ne_zero {ι : Type} [Fintype ι] {P Q R S : ι → ℕ} :
    (PiTensorProduct.tprod ℂ fun w : ι => (1 : Pol (P w) (Q w) (R w) (S w))) ≠ 0 := by
  intro h
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap
    fun w => (MvPolynomial.aeval (R := ℂ) (S₁ := ℂ) (σ := Ln (P w) (Q w) (R w) (S w)) fun _ => 0).toLinearMap)) h
  simp at this

theorem vacLineD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → IsStd ψ →
    FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ → ∀ (f₀ : SInf F κ) (ε : InfinitePlace F → ℤˣ),
    (∀ u u' : Matrix α β (AE F E), At (evI F) u → At (evI F) u' → ∀ c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ,
      (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) →
      (∀ w, u'.map (piInf (τ w)) = A w * ((((ε w : ℤ) : ℂ) * Complex.I) • (Jm (P w) (Q w) * c w * Jm (R w) (S w))) * (C w)ᵀ) →
      ∀ f f' : SInf F κ, SD (fun t => d.rho ψ (realAd F t • u)) f₀ f → SD (fun t => d.rho ψ (realAd F t • u')) f₀ f' →
        f' = Complex.I • f) →
    ∃ z : ℂ, f₀ = z • Φ (PiTensorProduct.tprod ℂ fun _ => 1) := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ hCM hStd hFr hΦ f₀ ε hyp
  have hD : DerEx := GlobalTheory.T.archHeisenbergDerivatives_exist
  obtain ⟨D, hDu⟩ := hD F E σ α β κ ψ JA JB d hStd
  obtain ⟨J, e, e', hJ, he, hJe, he1, he2, hy⟩ := GlobalTheory.T.exists_archimedeanPhaseSpace_complexStructure_signatures F E σ α β κ P Q R S τ JA JB d a b A C ε hCM hFr
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
  have hg0 : g₀ ≠ 0 := fun h => vacD_ne_zero (hΦ.1 (h.trans (map_zero Φ).symm))
  have hg : ∀ y x, fderiv ℝ g₀ x (J y).1 - 2 * Real.pi * Complex.I * (trPair F κ x (J y).2 : ℝ) * g₀ x =
      Complex.I * (fderiv ℝ g₀ x y.1 - 2 * Real.pi * Complex.I * (trPair F κ x y.2 : ℝ) * g₀ x) := by
    intro y x
    obtain ⟨u, -, u₁, c, hu, -, hu₁, hc, -, hc₁, h0, -, h1⟩ := hy y
    have e0 := GlobalTheory.T.hasArchDerivativeOnPureTensor_unique_adelicOperators (hDu u hu g₀).1 (hΦ.2 u hu c hc _)
    have e1 := GlobalTheory.T.hasArchDerivativeOnPureTensor_unique_adelicOperators (hDu u₁ hu₁ g₀).1 (hΦ.2 u₁ hu₁ _ hc₁ _)
    rw [GlobalTheory.T.fock_vacuum_pi_tensor_heisenberg_factorwise_signature, map_smul, ← e0] at e1
    have := congrArg (fun g : SInf F κ => g x) e1
    simp only [SchwartzMap.smul_apply, smul_eq_mul] at this
    rw [hDx u hu, hDx u₁ hu₁, h0, h1] at this
    exact this
  obtain ⟨z, hz⟩ := GlobalTheory.T.schwartz_complexStructure_vacuum_solution_eq_smul (trPair F κ) (fun y h => GlobalTheory.T.archimedeanTracePairingBilinear_nondegenerate y h) J e e' hJ he hJe he1 he2 f₀ g₀ hg0 hg hf
  exact ⟨z, hz⟩

end GlobalTheory.HoweD

end
