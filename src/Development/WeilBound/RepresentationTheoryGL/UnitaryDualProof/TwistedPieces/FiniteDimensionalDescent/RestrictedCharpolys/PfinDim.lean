module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.PullPieces
import GroundTheory.AutomorphicForms.GLnLocal
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open ValuativeRel

namespace PositivityTheory.RgUd.TP.Desc.Restr.PfinDim

open PositivityTheory.RgUd.TP.Desc.Restr

theorem finDim (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    FinDim k := by
  intro p c _ _
  letI := frMod (k := k) p c
  letI := IsTopologicalAddGroup.rightUniformSpace k
  have := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  have hc : CompleteSpace k := inferInstance
  letI : NontriviallyNormedField k := Valued.toNontriviallyNormedField k (ValueGroupWithZero k)
  have : CompleteSpace k := hc
  have : IsTopologicalAddGroup (Fr k p c) := inferInstanceAs (IsTopologicalAddGroup k)
  have : T2Space (Fr k p c) := inferInstanceAs (T2Space k)
  have : LocallyCompactSpace (Fr k p c) := inferInstanceAs (LocallyCompactSpace k)
  have : Nontrivial (Fr k p c) := inferInstanceAs (Nontrivial k)
  have : ContinuousSMul k (Fr k p c) := ⟨by
    show Continuous fun q : k × k => (iterateFrobenius k p c q.1) * q.2
    simp only [iterateFrobenius_def]
    exact (continuous_fst.pow _).mul continuous_snd⟩
  have hfd : FiniteDimensional k (Fr k p c) := FiniteDimensional.of_locallyCompactSpace k
  exact ⟨hfd, Module.finrank_pos⟩

end PositivityTheory.RgUd.TP.Desc.Restr.PfinDim

end
