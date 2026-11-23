module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastBasicPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionNormalizedDerivWeierstrassPTorsionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassTorsionQCoefficientsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassDivisionValueQExpansionStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F

namespace GlobalTheory.WpFam.ExpansionIntegral

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (N : ℕ) [NeZero N] (M : ℕ)
    (x : Fin 2 → ZMod N), ¬ l ∣ M → M • x = 0 → x ≠ 0 →
    QAll (Sz l lam 0) N (wB N x) ∧ QAll (Sz l lam 0) N (wpd N x) := by
  intro l hl lam N _ M x hM hx hx0
  have hpos : 0 < M := Nat.pos_of_ne_zero fun h => hM (h ▸ dvd_zero l)
  have hpow : ∀ e : ℕ, ¬ l ∣ M ^ e := fun e h => hM (hl.out.dvd_of_dvd_pow h)
  have hsz := (GlobalTheory.T.algebraicValuationAtLeast_basic_properties l lam).1
  refine ⟨⟨cB N x, GlobalTheory.T.weierstrass_division_value_q_expansion N x hx0, fun k => hsz (M ^ 2) _ (hpow 2) ?_⟩,
    ⟨cD N x, GlobalTheory.T.hasQExpansion_normalizedDerivWeierstrassPTorsion N x, fun k => hsz (M ^ 3) _ (hpow 3) ?_⟩⟩
  · rw [Nat.cast_pow]
    exact (GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients N M x k hpos hx).1
  · rw [Nat.cast_pow]
    exact (GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients N M x k hpos hx).2.1

end GlobalTheory.WpFam.ExpansionIntegral
