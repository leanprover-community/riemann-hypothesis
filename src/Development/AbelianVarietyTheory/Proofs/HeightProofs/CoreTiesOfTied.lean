module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.RunsAlong
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoreTiesOfHyp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Plug
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Plug.coreTies_of_tied : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (L : SizeData₂ D) (EX : ErrX D) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : Formalism.IndefR.Links.RealDat D A J.Q.c.F) (μ0 : T0), Tied EX J R.C → R.toLevCh.Is μ0 → FieldSmall D L → GlobalTheory.BigOn.CoreTies L EX J R := by
  intro D G _ _ Pl0 T0 A L EX J _ R μ0 hT hL hs
  have hH : HalfEX J.toCore EX := fun i => by
    show barE D (EX.piG i) ∈ (J.pb i).asIdeal.map _
    rw [hT.core.pb]
    exact hT.half i
  exact GlobalTheory.BigOn.coreTies_of_is hL hT.core.pb hT.core.laws hT.core.canon hT.core.rank hH hT.field.one hT.field.two hs
    hT.field.del hT.field.del'
