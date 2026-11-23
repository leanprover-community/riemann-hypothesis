module

public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.Group.Defs
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Mathlib.Topology.Algebra.OpenSubgroup

@[expose] public section

open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

namespace GlobalTheory.CompanionTheory.OrbitalCount

theorem relIndex_open_compact_and_twisted :
    ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (K L : Subgroup H),
      IsOpen (L : Set H) → IsCompact (K : Set H) → L ≤ K → L.relIndex K ≠ 0 ∧
        ∀ (T C : Subgroup H) (x : H),
          (T ⊓ K.map (MulAut.conj x).toMonoidHom).relIndex C ≠ 0 →
            (T ⊓ L.map (MulAut.conj x).toMonoidHom).relIndex C ≠ 0 := by
  intro H _ _ _ K L hL hK hLK
  have hKL : L.relIndex K ≠ 0 := by
    haveI := isCompact_iff_compactSpace.mp hK
    haveI : Finite (K ⧸ L.subgroupOf K) :=
      Subgroup.quotient_finite_of_isOpen _ (hL.preimage continuous_subtype_val)
    exact Subgroup.index_ne_zero_of_finite
  refine ⟨hKL, fun T C x hC => ?_⟩
  have hf : Function.Injective (MulAut.conj x).toMonoidHom := (MulAut.conj x).injective
  have h1 : (L.map (MulAut.conj x).toMonoidHom).relIndex (K.map (MulAut.conj x).toMonoidHom) ≠ 0 := by
    rwa [Subgroup.relIndex_map_map_of_injective L K hf]
  have h2 : (L.map (MulAut.conj x).toMonoidHom).relIndex (T ⊓ K.map (MulAut.conj x).toMonoidHom) ≠ 0 :=
    fun h => h1 (Subgroup.relIndex_eq_zero_of_le_right inf_le_right h)
  have h3 : T.relIndex (T ⊓ K.map (MulAut.conj x).toMonoidHom) ≠ 0 := by
    rw [Subgroup.relIndex_eq_one.mpr inf_le_left]
    exact one_ne_zero
  exact Subgroup.relIndex_ne_zero_trans (Subgroup.relIndex_inf_ne_zero h3 h2) hC

end GlobalTheory.CompanionTheory.OrbitalCount
