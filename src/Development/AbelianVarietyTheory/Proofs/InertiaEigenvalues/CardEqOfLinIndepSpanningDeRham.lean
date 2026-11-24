module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiSTmul

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
open GlobalTheory.HodgeAt

namespace GlobalTheory

theorem card_eq_of_indep_spans_dR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (a m : ℕ) (w : Fin m → Fin a → P.R.BdR), (∀ β : Fin m → P.R.BdR, ∑ i, β i • w i = 0 → β = 0) → (∀ j, ∃ u : Fin m → P.R.BdR, ∑ i, u i • w i = Pi.single j 1) → m = a := by
  intro l _ P AI T a m w hind hspan
  haveI : Nontrivial P.R.BdR := (GlobalTheory.DRFil.isField_dR T).nontrivial
  have hli : LinearIndependent P.R.BdR w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    exact congrFun (hind g hg) i
  have h1 : m ≤ a := by
    have := hli.fintype_card_le_finrank
    simpa [Module.finrank_fin_fun] using this
  have hsurj : Function.Surjective (Fintype.linearCombination P.R.BdR w) := by
    rw [← LinearMap.range_eq_top, Submodule.eq_top_iff']
    intro x
    have hj : ∀ j, Pi.single j (x j) ∈ LinearMap.range (Fintype.linearCombination P.R.BdR w) := by
      intro j
      obtain ⟨u, hu⟩ := hspan j
      refine ⟨x j • u, ?_⟩
      rw [map_smul, Fintype.linearCombination_apply, hu]
      ext k
      by_cases h : k = j
      · subst h; simp
      · simp [Pi.single_apply, h]
    rw [← Finset.univ_sum_single x]
    exact Submodule.sum_mem _ fun j _ => hj j
  have h2 : a ≤ m := by
    simpa using card_le_of_surjective P.R.BdR _ hsurj
  exact le_antisymm h1 h2

end GlobalTheory
