module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
public import Development.AbelianVarietyTheory.Counterexamples.HeckeCharacterExamples.PeriodBoundOfPlaceBound
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsStagesClauses
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemNonzeroPlacesOfResidueChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.GalLoc
theorem twistedAt_atMem_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => ∃ v, TwistedAt (w.D Z) v := by
  intro hL
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c _ _ _ => ?_
  obtain ⟨v, hv⟩ := GlobalTheory.Survey.PeriodBoundOfPlaceBound.exists_place (w.D Z) (B.host.g 0) (B.host.g_prime 0)
  have hW := GlobalTheory.Mem.Top.Bl.Model3.type_mem t v 0 hv
  exact ⟨v, (GlobalTheory.Mem.Top.V4.Model.mem_iff t.mu v).1 hW⟩
end GlobalTheory.GalLoc
end
