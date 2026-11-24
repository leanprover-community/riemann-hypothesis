module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenericUnlinkedGLOutright
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GenericLDatum

theorem exists_unlinked_isL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (x : IrrGL (k := k)), IsGeneric x.rep →
    ∃ (c : ℕ) (Δ : Fin c → Segment k), (∀ i j, i ≠ j → ¬ (Δ i).Linked (Δ j)) ∧
      IsL ((List.ofFn Δ : List (Segment k)) : Multiset (Segment k)) x.rep := by
  intro k _ _ _ _ _ x hg
  obtain ⟨c, Δ, y, hd, hun, hL, ⟨e⟩⟩ :=
    GlobalTheory.genericUnlinkedGL_outright k x.1 _ x.rep x.2.rep.smooth x.2.rep.irr hg
  refine ⟨c, Δ, hun, c, y, hd, ⟨Δ, ⟨?_, ?_⟩, hL⟩, (isCosocle_self x.2.rep.irr).of_equiv (.refl _) e⟩
  · exact Fin.univ_val_map Δ
  · intro i j hij hP
    exact hun i j (ne_of_lt hij) hP.1

end GlobalTheory.GenericLDatum
