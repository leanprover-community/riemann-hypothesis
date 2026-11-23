module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AppellHumbertFrameSemicharacterStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaConstantOfThetaGroupStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ReadingOfThetaGroupActionStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaConstSymmetricSquareEqOneStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaConstantPowEqOneOfPowerTrivialStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem rd_fock_of_symLift : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), (∀ a ∈ Φ.lat, Φ.χ a ^ 2 = 1) → ∀ (k : ℤ) (n : ℕ) (U : ThetaGrp A L.L k (Over.mk x0)) (x δ : Fin g → ℂ) (s s' : LB.Sec (LPow A L.L k (Over.mk x0))) (θ : (Fin g → ℂ) → ℂ), Odd n → δ ∈ Φ.lat → (n : ℂ) • x = (2 : ℂ) • δ → SymLift A L.L k n (Φ.e x) U → IsActOf A L.L k U s s' → Φ.Rd k s θ → Φ.Rd k s' (fock Φ.Hm k x θ) := by
  intro S A _ _ L x0 g Φ hχ k n U x δ s s' θ hn hδ hnx hU hact hrd

  obtain ⟨c, -, hc⟩ := GlobalTheory.T.exists_thetaConstant_of_thetaGroup S A L x0 g Φ k U x hU.1
  have hread := GlobalTheory.T.reading_of_thetaGroup_action S A L x0 g Φ k U x c s s' θ hc hact hrd

  have hsq : c ^ 2 = 1 := GlobalTheory.T.thetaConst_symmetric_square_eq_one S A L x0 g Φ k U x c hc hU.3

  have hmem : (n : ℂ) • x ∈ Φ.lat := by
    rw [hnx, two_smul]
    exact add_mem hδ hδ
  have hχδ : Φ.χ ((2 : ℂ) • δ) = 1 := (GlobalTheory.T.appellHumbert_frame_semicharacter S A L x0 g Φ).2.2 hχ δ hδ
  have hpow := GlobalTheory.T.thetaConstant_pow_eq_one_of_power_trivial S A L x0 g Φ k n U x c hc hmem hU.2
  rw [hnx, hχδ, one_zpow, _root_.mul_one] at hpow

  have hc1 : c = 1 := by
    obtain ⟨m, rfl⟩ := hn
    rw [pow_succ, pow_mul, hsq, one_pow, _root_.one_mul] at hpow
    exact hpow
  subst hc1
  simpa only [_root_.one_mul] using hread

end GlobalTheory.AnVal
