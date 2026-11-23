module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
public import Formalism.QuotientMetricDivisors.Statement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
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
import Mathlib.Tactic.Linter.Style
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

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoverConj

theorem isConjugatePlace_conjugateIdealPlace (D : D7) (P : Pl D.host.E) : Formalism.L2.DIV.IsConjPl P (Formalism.DivisionValues.conjPl P) := by
  intro a b hab
  have hb : b = Formalism.DivisionValues.cO D.host.E a := RingOfIntegers.ext (by rw [hab]; rfl)
  subst hb
  show a ∈ P.asIdeal ↔ Formalism.DivisionValues.cO D.host.E a ∈ P.asIdeal.map (Formalism.DivisionValues.cO D.host.E)
  constructor
  · exact fun h => Ideal.mem_map_of_mem _ h
  · intro h
    rw [Ideal.mem_map_of_equiv] at h
    obtain ⟨x, hx, hxa⟩ := h
    rwa [← (Formalism.DivisionValues.cO D.host.E).injective hxa]

theorem cover : ∀ (D : D7) (Pg : Finset (Pl D.host.E)), GlobalTheory.Core.Mi.IsTypePlaces Pg → ∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ PP ∈ Pg, Q = PP ∨ ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (resS D.host.F Q s = 0 ↔ resS D.host.F PP (sigInt (instOf D) s) = 0) := by
  intro D Pg hPg Q hQ
  have hv : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ (Q.under (𝓞 D.host.F)).asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ Q.asIdeal
    rw [map_natCast]
    exact hQ
  obtain ⟨PP, ⟨hPP, hunder⟩, -⟩ := hPg.2 _ hv
  refine ⟨PP, hPP, ?_⟩
  rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hunder.symm with h | h
  · exact Or.inl h
  · right
    intro s
    have hc : Formalism.L2.DIV.IsConjPl PP Q := h ▸ isConjugatePlace_conjugateIdealPlace D PP
    exact (Formalism.L2.DIV.resS_sigS_eq_zero_iff (instOf D).cm hc.symm s).symm

end GlobalTheory.CoverConj
