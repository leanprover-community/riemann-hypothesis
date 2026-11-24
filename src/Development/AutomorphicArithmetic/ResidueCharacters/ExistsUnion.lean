module

public import Development.AutomorphicArithmetic.ResidueCharacters.InvariantsKilledOverCyclotomicAlt
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Development.AutomorphicArithmetic.CyclotomicBounds.FiniteDimensionalRoots
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

namespace UpperTheory.N

def CycAt {D : D7} (N : ℕ) (i : D.nd.Loc) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw),
    Cyc N (D.nbr i w hw).Kw C.LL

theorem cycAt_of {D : D7} (i : D.nd.Loc) (h2 : D.nd.l i = 2 → 4 ∣ D.host.condN) : CycAt D.host.condN i :=
  fun w hw C => ⟨h2, Nat.pos_of_ne_zero D.host.toHostRaw.condN_ne_zero,
    UpperTheory.KStar.Cyc.kw_le_roots D.host.toHostRaw (D.nbr i w hw), C.isGood⟩

theorem exists_union {ι : Type} [Finite ι] (a n h : ℕ) (hc : Nat.card ι ≤ a) (p : ι → ℤ → Prop)
    (H : ∀ τ, ∃ U : Finset ℤ, U.card ≤ n ∧ (∀ u ∈ U, -(h : ℤ) ≤ u ∧ u ≤ h) ∧ ∀ x, p τ x → x ∈ U) :
    ∃ U : Finset ℤ, U.card ≤ a * n ∧ (∀ u ∈ U, -(h : ℤ) ≤ u ∧ u ≤ h) ∧ ∀ τ x, p τ x → x ∈ U := by
  classical
  haveI := Fintype.ofFinite ι
  choose U h1 h2 h3 using H
  refine ⟨Finset.univ.biUnion U, ?_, ?_, fun τ x hx => Finset.mem_biUnion.2 ⟨τ, Finset.mem_univ _, h3 τ x hx⟩⟩
  · refine Finset.card_biUnion_le.trans ((Finset.sum_le_card_nsmul _ _ n fun τ _ => h1 τ).trans ?_)
    rw [smul_eq_mul, Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact Nat.mul_le_mul_right _ hc
  · intro u hu
    obtain ⟨τ, -, hτ⟩ := Finset.mem_biUnion.1 hu
    exact h2 τ u hτ

end UpperTheory.N

end
