module

public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianUnitFormDiagonalizesStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianUnitFormRepresentsUnitStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorInvolutionAlgebraPropertiesStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem hermR_unit_diagonalisable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [IsArtinianRing R] [IsReduced R] (n : ℕ) (S : HermR R σ n), IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det → ∃ (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (d : Fin n → Rˣ), IsUnit g.det ∧ (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) g * Matrix.diagonal (fun i => ((d i : R) ⊗ₜ[F] (1 : E) : R ⊗[F] E)) * g := by
  intro F E _ _ _ _ _ σ hσ R _ _ _ _ n S hS
  obtain ⟨hart, -, h2, hinv, hδ, hfix, hunit⟩ := GlobalTheory.T.tensor_involution_algebra_properties F E σ hσ R
  haveI : IsArtinianRing (R ⊗[F] E) := hart
  haveI : Finite (MaximalSpectrum (R ⊗[F] E)) := inferInstance
  have hrep := GlobalTheory.T.hermitian_unit_form_represents_unit (R ⊗[F] E) (sigR R σ) hinv h2 hδ
  obtain ⟨g, d, hg, hd, hgd⟩ :=
    GlobalTheory.T.hermitian_unit_form_diagonalizes (R ⊗[F] E) (sigR R σ) hinv hrep n (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) S.2 hS
  choose r hr using fun i => hfix (d i) (hd i).2
  have hru : ∀ i, IsUnit (r i) := fun i => (hunit (r i)).1 (hr i ▸ (hd i).1)
  have hgi : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hg
  have hdiag : Matrix.diagonal (fun i => (((hru i).unit : R) ⊗ₜ[F] (1 : E) : R ⊗[F] E)) = Matrix.diagonal d := by
    congr 1
    funext i
    simp [hr i]
  refine ⟨g⁻¹, fun i => (hru i).unit, Matrix.isUnit_nonsing_inv_det g hg, ?_⟩
  rw [hdiag, ← hgd]
  have hc : cT (sigR R σ) g⁻¹ * cT (sigR R σ) g = 1 := by
    rw [← cT_mul, hgi, cT_one]
  calc (S : Matrix (Fin n) (Fin n) (R ⊗[F] E))
      = (cT (sigR R σ) g⁻¹ * cT (sigR R σ) g) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (g * g⁻¹) := by
        rw [hc, hgi, one_mul, mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.SW
