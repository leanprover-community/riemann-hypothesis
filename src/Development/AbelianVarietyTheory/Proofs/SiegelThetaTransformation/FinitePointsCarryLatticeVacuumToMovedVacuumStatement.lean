module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FinitePointsCarryLatticeVacuumToMovedVacuum
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finitePoints_carry_latticeVacuum_to_moved_vacuum : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → ∀ w : D.host.E, IsIntegral ℤ w → w + cc w = 1 → IdemTwo w → ∀ (M : ℕ), ∀ Λ ∈ Vset D.host.E S.rank M, ∀ Λ' ∈ Vset D.host.E S.rank M, ∀ L L' : Lt D.host.E T.rank, SelfD C.X L → SelfD C.X L' → ∀ h ∈ GfC S, ∀ g ∈ GfC T, IsMov (fmtC S h) Λ Λ' → IsMov (fmt T g) L L' → ∀ v v', IsVac C.X C.bas w (tens Λ L) v → IsVac C.X C.bas w (tens Λ' L') v' → ∀ B, C.IsB B → ∃ c : ℂ, ‖c‖ = 1 ∧ om (h, g) (C.Th (C.xB B) v) = c • (C.Th (C.xB B) v') := by
  first | exact @GlobalTheory.Ker.om_Th_vac | exact GlobalTheory.Ker.om_Th_vac | (intros; apply GlobalTheory.Ker.om_Th_vac <;> assumption)
