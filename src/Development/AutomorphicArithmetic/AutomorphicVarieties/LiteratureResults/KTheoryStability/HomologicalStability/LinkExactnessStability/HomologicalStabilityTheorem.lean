module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KAcyclicHomology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.GroupHomologyGLStabInjectiveOfStableRangeInducti
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.GroupHomologyGLStabSurjectiveOfStableRangeInduct
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL

namespace GlobalTheory.HomStab

theorem kStability_main : UpperTheory.V.Published.KStability := by
  intro R _ s hs
  have key : ∀ i : ℕ, ∀ m m' (h : m ≤ m'), m' = m + 1 →
      (2 * i + s + 1 ≤ m → Function.Surjective (grpHMap (stab R m m' h) i).hom) ∧
      (2 * i + s + 2 ≤ m → Function.Injective (grpHMap (stab R m m' h) i).hom) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      have hyp : ∀ q m m' (h : m ≤ m'), q < i → m' = m + 1 →
          (2 * q + s + 1 ≤ m → Function.Surjective (grpHMap (stab R m m' h) q).hom) ∧
          (2 * q + s + 2 ≤ m → Function.Injective (grpHMap (stab R m m' h) q).hom) :=
        fun q m m' h hq hm => ih q hq m m' h hm
      intro m m' h hm
      exact ⟨GlobalTheory.T.groupHomology_GL_stab_surjective_of_stableRange_induction R s hs i hyp m m' h hm, GlobalTheory.T.groupHomology_GL_stab_injective_of_stableRange_induction R s hs i hyp m m' h hm⟩
  intro i n hn
  have h1 := key i n (n + 1) (Nat.le_succ n) rfl
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨(h1.2 hn), (h1.1 (by omega))⟩

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL
end
