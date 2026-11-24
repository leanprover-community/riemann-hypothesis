module

public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.IsSchwartzBruhatOfProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountableStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilConvergentRangeStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilOrbitalIntegralFormula
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

theorem coefN_finset_sum_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx → ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db → ∀ (T : Matrix (Fin n) (Fin n) E) (N : ℕ) (Φ : Fin N → (Fin n → Fin M → AF F ⊗[F] E) → ℂ), (∀ i, IsSchwartzBruhat (Φ i)) → coefN σ J ψ dx db (fun X => ∑ i, Φ i X) T = ∑ i, coefN σ J ψ dx db (Φ i) T := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hM ψ hψ dx hdx db hdb T N Φ hΦ
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, ht, -, hB, -, hG⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)
  haveI := hB n M
  obtain ⟨hψc, hψn, -⟩ := id hψ
  have hstar : ∀ b, starN σ J ψ dx (fun X => ∑ i, Φ i X) b = ∑ i, starN σ J ψ dx (Φ i) b := by
    intro b
    unfold starN
    simp_rw [Finset.sum_mul]
    refine integral_finsetSum _ fun i _ => ?_
    obtain ⟨hc, hi⟩ := GlobalTheory.CompanionTheory.SiegelND.CoefSum.continuous_integrable_tuple σ hCM M n dx hdx.1 (Φ i) (hΦ i)
    have hq : Continuous fun X : Fin n → Fin M → AF F ⊗[F] E =>
        algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
          (Matrix.trace ((b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J X)) :=
      continuous_const.mul (ht.comp (continuous_const.matrix_mul (hG n M J)).matrix_trace)
    refine hi.norm.mono' (hc.mul (hψc.comp hq)).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_mul, hψn, mul_one]
  unfold coefN
  simp_rw [hstar, Finset.sum_mul]
  refine integral_finsetSum _ fun i _ => ?_
  have hI := GlobalTheory.T.siegel_weil_convergent_range F E σ hCM M J hJ n hM ψ hψ dx hdx db hdb (Φ i) (hΦ i)
  have hc : Continuous fun b : HermR (AF F) σ n =>
      ψ (-(algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
        (Matrix.trace (T.map (inclR (AF F)) * (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)))))) :=
    hψc.comp (continuous_const.mul
      (ht.comp (continuous_const.matrix_mul continuous_subtype_val).matrix_trace)).neg
  haveI : BorelSpace (HermR (AF F) σ n) := ⟨rfl⟩
  refine hI.norm.mono' (hI.1.mul hc.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun b => ?_
  rw [norm_mul, hψn, mul_one]

end GlobalTheory.CompanionTheory.SiegelND.Coef
