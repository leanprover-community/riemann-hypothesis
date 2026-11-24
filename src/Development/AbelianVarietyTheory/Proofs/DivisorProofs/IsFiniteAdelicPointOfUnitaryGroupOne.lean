module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ClassFunctionSumIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCongLevelIntG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacTheta

@[expose] public section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BotFormula

theorem isFinPt_one : ∀ {D : D7} (V : HSp D) {n : ℕ}, V.rank = n → IsFinPt V (1 : GA D V) (1 : Formalism.MainNotions.StandardLatticesGL3.GA D n) := by
  intro D V n hn
  subst hn
  refine ⟨one_mem _, rfl, fun i j => ?_⟩
  have hL : (finHom V (1 : GA D V)).val = 1 := by
    rw [map_one]; rfl
  rw [hL, Fin.cast_eq_self, Fin.cast_eq_self]
  show _ = toFinE D ((1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j)
  by_cases hij : i = j
  · subst hij; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one, map_one]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero, map_zero]

end GlobalTheory.BotFormula
