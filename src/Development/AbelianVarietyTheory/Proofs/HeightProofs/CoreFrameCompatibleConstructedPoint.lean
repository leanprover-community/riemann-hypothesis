module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.RunsAlong
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjGeneratorsMemFramePrimesTrueColumnsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndexBoundCoefficientFieldOfExactSmallFieldStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Plug
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Plug

theorem tied_cfOf : GlobalTheory.NT.RayField → ∀ (𝒮 : Slots), CoreSlot 𝒮 → ∀ (K : Ctx) (p : WPt 𝒮 K), Tied p.O.ex.errX (cfOf p).J (cfOf p).C := by
  intro hR 𝒮 hcs K p
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact p.x.what₂.r.z.geo.fw.laws
  · exact hcs K p.B p.f p.T p.w p.Z p.x.Wt p.O.p0 p.x.what₂ p.x.rx
  · exact GlobalTheory.T.fieldTies_of_rayField_of_ksExact hR (p.w.st p.Z) p.f p.w.δ p.w.exact
  · show HalfAt (ofObj p.O).errX (Fr.at (p.w.st p.Z) p.f)
    rw [p.x.errX]
    exact GlobalTheory.T.conjGenerators_mem_framePrimes_trueColumns p.B p.f p.T p.w p.Z p.x.col.toColT

end GlobalTheory.Plug
