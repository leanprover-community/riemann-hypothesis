module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastBasicPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenominatorBoundWeierstrassCmTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinWeierstrassValuesLatticeTauStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneityOfIsTauOfStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImagQuadIntegerLatticeMulStableISqrtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralJInvariantOfComplexMultiplicationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JTEqAndPowTwelveEqDD
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastMulTorsMemLatticeIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOfLatticeTauLatticeMembership
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.SzTau

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (d : ℕ) (Λ : PeriodPair) (c Ω : ℂ) (τ : ℍ), d.Prime → 4 < d → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ → IsTauOf Λ c τ → Ω ^ 12 = latDisc Λ → (Ω * c / (2 * Real.pi * Complex.I)) ^ 12 = DD τ ∧ Sz l lam 0 (jT τ) ∧ ∀ (N : ℕ) [NeZero N] (M : ℕ) (x : Fin 2 → ZMod N), ¬ l ∣ M → M • x = 0 → x ≠ 0 → Sz l lam (if l = 2 then (if d % 4 = 3 then 1 else 2) else if l = d then 1 / 2 else 0) ((G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 + wp N x τ) / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2) := by
  intro l hl lam d Λ c Ω τ hd h4 hΛ hτ hΩ
  obtain ⟨hst, him⟩ := GlobalTheory.T.imagQuadIntegerLattice_mulStable_I_sqrt d Λ hd.pos hΛ
  refine ⟨GlobalTheory.QFam.pow_twelve_eq_DD Λ c τ hτ Ω hΩ, ?_, ?_⟩
  · refine (GlobalTheory.T.algebraicValuationAtLeast_basic_properties l lam).1 1 (jT τ) hl.out.not_dvd_one ?_
    rw [Nat.cast_one, one_mul]
    exact GlobalTheory.T.isIntegral_jInvariant_of_complexMultiplication Λ c τ _ hτ hst him
  · intro N _ M x hM hx hx0
    obtain ⟨h1, h2⟩ := GlobalTheory.T.eisensteinWeierstrass_values_lattice_tau Λ c Ω τ hτ
    rw [add_div, h1, (h2 N x).1, ← add_div]
    have hh := (GlobalTheory.T.weierstrassP_homogeneity_of_isTauOf Λ c τ hτ).1
    refine GlobalTheory.T.denominator_bound_weierstrass_cm_torsion l lam d Λ Ω _ M hd h4 hst hΩ hM ?_ ?_
    · rw [hh, (GlobalTheory.WpFam.TorsMem.main N τ).2.2.1 x]
      exact hx0
    · rw [mul_left_comm, hh]
      exact (GlobalTheory.WpFam.natCast_mul_tors_mem_lattice_iff N τ M x).2 hx

end GlobalTheory.SzTau
