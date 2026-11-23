module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReversedMinorProductMemHarmonicRowHighest
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.reversedMinorProduct_mem_harmonicRowHighest : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), T.rank ≤ S.rank → ∀ (ap am : D.what₂.Tau → ℕ → ℕ), ∃ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ), C.toH (MvPolynomial.rename (fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2)) (Formalism.IndefR.Datum.delta (m := T.rank) (n := S.rank) (fun _ => C.X.p0) (fun _ => C.q0) ap am)) ∈ Harm.rowHighest ℂ c c' ∧ C.toH (MvPolynomial.rename (fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2)) (Formalism.IndefR.Datum.delta (m := T.rank) (n := S.rank) (fun _ => C.X.p0) (fun _ => C.q0) ap am)) ≠ 0 := by
  first | exact @GlobalTheory.RenamedMinors.renamed_delta_mem_rowHighest | exact GlobalTheory.RenamedMinors.renamed_delta_mem_rowHighest | (intros; apply GlobalTheory.RenamedMinors.renamed_delta_mem_rowHighest <;> assumption)
