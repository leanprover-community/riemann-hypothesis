module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApprox
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralUnitaryLiftIdempotentPart
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead


theorem _root_.GlobalTheory.T.exists_integral_unitary_lift_idempotentPart : ∀ {D : D7} (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS →
  ∀ {a : ℕ} (N : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)), (∀ i j, N i j ∈ OhE D) →
  ∀ x : (AE D)ˣ, IsUnitDet e (N.map (toE D)) x → ∃ k : Formalism.MainNotions.StandardLatticesGL3.GA D a, k ∈ intG D a ∧
    ∀ i j, GlobalTheory.BotClassDict.finQ D e * (((k : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
      Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j = GlobalTheory.BotClassDict.finQ D e * N i j := by
  first | exact @GlobalTheory.StdRead.IntLift.exists_lift | exact GlobalTheory.StdRead.IntLift.exists_lift | (intros; apply GlobalTheory.StdRead.IntLift.exists_lift <;> assumption)
