module

public import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffEqZeroOfEvAEqZeroOfLeFinrankStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesGenerateConnectedLevelsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankOmegaLeFinrankFrobeniusKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalAtNilpotentXEqCoordinateStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem evA_comp_coe {K A : Type} [Field K] [CommRing A] [Algebra K A] {d : ℕ}
    (x : Fin d → A) (hx : ∀ i, IsNilpotent (x i)) :
    (evA K x hx).comp (MvPolynomial.coeToMvPowerSeries.algHom K) = MvPolynomial.aeval x := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply, MvPolynomial.aeval_X]
  simp only [MvPolynomial.coe_X, map_X]
  exact GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate K (Fin d) A x hx i

theorem exists_chart_of_isConn (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0)
    (G : PDivGroup p K) (hG : G.IsConn) : ∃ d, Nonempty (Chart G d) := by
  obtain ⟨x, hres, haug, hsurj⟩ := GlobalTheory.T.exists_coordinates_generate_connected_levels p K h G hG
  have hmem : ∀ n i, x n i ∈ augIdeal K (G.A n) := fun n i => by
    simp [augIdeal, haug n i]
  have hnil : ∀ n i, IsNilpotent (x n i) := fun n i => hG n _ (hmem n i)
  refine ⟨_, ⟨{ x := x, nil := hnil, res := hres, aug := haug, presents := ⟨?_, ?_⟩ }⟩⟩
  · intro n a
    obtain ⟨P, hP⟩ := hsurj n a
    refine ⟨(P : MvPowerSeries _ K), ?_⟩
    have := congrArg (fun φ => φ P) (evA_comp_coe (x n) (hnil n))
    simp only [AlgHom.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply] at this
    rw [← hP, ← this]
    rfl
  · intro N
    refine ⟨N, fun f hf α hα => ?_⟩
    have hq : ∀ i, x N i ^ (p ^ N) ∈ frobKerIdeal (p ^ N) K (G.A N) :=
      fun i => pow_mem_frobKerIdeal (hmem N i)
    exact GlobalTheory.T.coeff_eq_zero_of_evA_eq_zero_of_le_finrank' K (G.A N) _ (p ^ N) (x N) (hnil N) _ (hsurj N) hq
      (GlobalTheory.T.pow_finrank_omega_le_finrank_frobeniusKernel p K h G N) f hf α
      (lt_of_lt_of_le hα (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le)

end GlobalTheory.Katz
