module

public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.SatakeDualWeyl.StatementE
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPrimeGLChartOfUnitaryGroup
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_splitPrime_GL_chart_of_unitaryGroup : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e P → ∀ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ∃ ρ : GA D V →* GL (Fin V.rank) (P.adicCompletion D.host.E), (∀ M : GL (Fin V.rank) (P.adicCompletion D.host.E), ∃ g, Formalism.L2.Theta.SuppAt e V g ∧ ρ g = M) ∧ (∀ k ∈ KsphC V ∅, ρ k ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov D.host.E P)) ∧ ∀ (g : GA D V) (a : Fin V.rank → ℤ), ∀ k₁ ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov D.host.E P), ∀ k₂ ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov D.host.E P), ((ρ g : GL (Fin V.rank) (P.adicCompletion D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion D.host.E)) = (k₁ : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion D.host.E)) * Formalism.UG.diagPow D.host.E P (algebraMap D.host.E (P.adicCompletion D.host.E) (ϖ : D.host.E)) a * (k₂ : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion D.host.E)) → DivAt V e (ϖ : D.host.E) (List.ofFn a) g := by
  first | exact @GlobalTheory.SplitPrimeChart.exists_chart | exact GlobalTheory.SplitPrimeChart.exists_chart | (intros; apply GlobalTheory.SplitPrimeChart.exists_chart <;> assumption)
