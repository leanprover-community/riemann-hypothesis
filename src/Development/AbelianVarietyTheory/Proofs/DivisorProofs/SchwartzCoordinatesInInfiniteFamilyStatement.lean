module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzCoordinatesInInfiniteFamily
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

open scoped TensorProduct ENNReal Matrix Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.schwartz_coordinates_in_infinite_family : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n d : ℕ) (ε : Module.Basis (Fin d) D.host.F D.host.E) (φ : WeilM.schA D.host.F (Fin m × Fin n × Fin d)), φ.1 ∘ coord ε ∈ GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ m n := by
  first | exact @GlobalTheory.SchwartzCoord.mem_schwartzA_comp_coord | exact GlobalTheory.SchwartzCoord.mem_schwartzA_comp_coord | (intros; apply GlobalTheory.SchwartzCoord.mem_schwartzA_comp_coord <;> assumption)
