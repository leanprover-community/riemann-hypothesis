module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergman
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergmanIntegrable
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergmanDensIntegrable
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanNorms
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsBis
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBergmanDensIntegrable
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBergmanIntegrable
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartBergmanBound
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartTaylorCover
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComplexTaylorTwo
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIntegralOfBergman
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLocalBergmanBound
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPolydiscSubmean
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PUniformBergmanBound
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

noncomputable section

lemma bergman_lerp_self {D : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    {A : FinHolAtlas D X} {L : HolLineBundle A} (W : Weight L) (t : ℝ) (dV : SmoothVolume A)
    (V : Submodule ℂ (Fin A.n → X → ℂ)) (n : ℕ) (x : X) :
    bergman (W.lerp W t) dV V n x = bergman W dV V n x := by
  simp only [bergman, sectionL2NormSq, ptNormSq, lerp_self_φ]

lemma bergman_nonneg {D : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    {A : FinHolAtlas D X} {L : HolLineBundle A} (W : Weight L) (dV : SmoothVolume A)
    (V : Submodule ℂ (Fin A.n → X → ℂ)) (n : ℕ) (x : X) : 0 ≤ bergman W dV V n x :=
  Real.iSup_nonneg fun _ => div_nonneg (ptNormSq_nonneg W n _ x) (sectionL2NormSq_nonneg W dV n _)

theorem BergmanL1Convergence.proof (hL1 : L1Convergence.Statement)
    (hLoc : LocalBergmanBound.Statement) (hUnif : UniformBergmanBound.Statement)
    (hInt : IntegralOfBergman.Statement) (hBI : BergmanIntegrable.Statement)
    (hDI : BergmanDensIntegrable.Statement) : BergmanL1Convergence.Statement := by
  intro D X _ _ _ _ _ A L W dV hW V _ hV hdim
  have := dV.isProb
  obtain ⟨C, hC⟩ := hUnif A L W W dV hW hW
  have hpos : ∀ n : ℕ, (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ D := fun n => by positivity
  set g : ℕ → X → ℝ := fun n x =>
    (((n + 1 : ℕ) : ℝ) ^ D)⁻¹ * bergman W dV (V (n + 1)) (n + 1) x with hg
  have hbound : ∀ n x, 0 ≤ g n x ∧ g n x ≤ C := fun n x => by
    refine ⟨mul_nonneg (inv_nonneg.2 (hpos n).le) (bergman_nonneg _ _ _ _ _), ?_⟩
    have h := hC (n + 1) (by omega) 0 ⟨le_rfl, zero_le_one⟩ (V (n + 1)) (hV _) x
    rw [bergman_lerp_self] at h
    show (((n + 1 : ℕ) : ℝ) ^ D)⁻¹ * bergman W dV (V (n + 1)) (n + 1) x ≤ C
    rw [inv_mul_le_iff₀ (hpos n)]
    linarith [mul_comm C (((n + 1 : ℕ) : ℝ) ^ D)]
  have hlim : ∀ (x : X) (ε : ℝ), 0 < ε → ∀ᶠ n in atTop, g n x ≤ bergmanDens W dV x + ε := by
    intro x ε hε
    have h := (tendsto_add_atTop_nat 1).eventually (hLoc A L W dV hW V hV x ε hε)
    filter_upwards [h] with n hn
    show (((n + 1 : ℕ) : ℝ) ^ D)⁻¹ * bergman W dV (V (n + 1)) (n + 1) x ≤ _
    rw [inv_mul_le_iff₀ (hpos n)]
    linarith [mul_comm (bergmanDens W dV x + ε) (((n + 1 : ℕ) : ℝ) ^ D)]
  have hmass : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∫ x, bergmanDens W dV x ∂dV.μ - ε ≤ ∫ x, g n x ∂dV.μ := by
    intro ε hε
    have h := (tendsto_add_atTop_nat 1).eventually (hdim ε hε)
    filter_upwards [h] with n hn
    have hI : ∫ x, g n x ∂dV.μ =
        (((n + 1 : ℕ) : ℝ) ^ D)⁻¹ * Module.finrank ℂ (V (n + 1)) := by
      rw [hg, integral_const_mul, hInt A L W dV (n + 1) (V (n + 1)) (hV _)]
    rw [hI, le_inv_mul_iff₀ (hpos n)]
    linarith [mul_comm (∫ x, bergmanDens W dV x ∂dV.μ - ε) (((n + 1 : ℕ) : ℝ) ^ D)]
  have hgi : ∀ n, Integrable (g n) dV.μ := fun n =>
    (hBI A L W dV (n + 1) (V (n + 1)) (hV _)).const_mul _
  have h := hL1 dV.μ g (bergmanDens W dV) C hgi (hDI A L W dV) hbound hlim hmass
  exact (tendsto_add_atTop_iff_nat 1).1 h

theorem BergmanL1Convergence.full : BergmanL1Convergence.Statement :=
  BergmanL1Convergence.proof L1Convergence.proof
    (LocalBergmanBound.proof (ChartBergmanBound.proof PolydiscSubmean.proof ComplexTaylorTwo.proof))
    (UniformBergmanBound.proof PolydiscSubmean.proof ChartTaylorCover.proof)
    IntegralOfBergman.proof BergmanIntegrable.proof BergmanDensIntegrable.proof

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
