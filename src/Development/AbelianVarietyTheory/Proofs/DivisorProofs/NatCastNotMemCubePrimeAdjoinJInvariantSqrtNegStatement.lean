module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CmCurveGoodOutsidePrimePremises
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastNotMemCubePrimeAdjoinJInvariantSqrtNeg
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
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.SemiChar

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.natCast_notMem_cube_prime_adjoin_jInvariant_sqrtNeg : ∀ (p : ℕ) (L₀ : PeriodPair) [NumberField ℚ⟮(latticeCurve L₀).j⟯] (w : HeightOneSpectrum (𝓞 ℚ⟮(latticeCurve L₀).j⟯)), p.Prime → IsIntegersLattice p L₀ → (p : 𝓞 ℚ⟮(latticeCurve L₀).j⟯) ∉ w.asIdeal ^ 3 := by
  first | exact @GlobalTheory.CMModel.natCast_notMem_pow_three_adjoin_j | exact GlobalTheory.CMModel.natCast_notMem_pow_three_adjoin_j | (intros; apply GlobalTheory.CMModel.natCast_notMem_pow_three_adjoin_j <;> assumption)
