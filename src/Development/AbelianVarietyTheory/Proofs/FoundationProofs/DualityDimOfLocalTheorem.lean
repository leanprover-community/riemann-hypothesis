module

public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.BlochKato₂

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

theorem localTheorem_iff (D : D7) : LocalSituation.Conclusion5 D ↔ BlochKatoReduction.adm3 D ∧
    ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l),
      LocalSituation.bkARightExact ((D.loc l).PD K) ∧ LocalSituation.bkC ((D.loc l).PD K) :=
  ⟨fun h => ⟨fun l _ K => ⟨(h l K).1, (h l K).2.1, (h l K).2.2.2.1⟩,
      fun l _ K => ⟨(h l K).2.2.1, (h l K).2.2.2.2⟩⟩,
    fun h l _ K => ⟨(h.1 l K).1, (h.1 l K).2.1, (h.2 l K).1, (h.1 l K).2.2, (h.2 l K).2⟩⟩

theorem duality_dim_of_localTheorem : ∀ D : D7, LocalSituation.Conclusion5 D → BlochKatoReduction.Gen.adm3 D ∧ BlochKatoReduction.adm3 D :=
  fun D h => ⟨((localTheorem_iff D).1 h).1, ((localTheorem_iff D).1 h).1⟩

end GlobalTheory.BlochKato₂
