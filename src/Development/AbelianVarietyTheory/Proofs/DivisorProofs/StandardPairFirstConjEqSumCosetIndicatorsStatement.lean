module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApprox
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairFirstConjEqSumCosetIndicators
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


theorem _root_.GlobalTheory.T.standardPairFirst_conj_eq_sum_cosetIndicators : ∀ {D : D7} (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d), a ≤ d → ∀ (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)), GoodMod e 𝔪 →
  ∀ ν : (AE D)ˣ →* Circle, KillsCong ν 𝔪 → ∀ β : GL (Fin S.rank) (EAf D), IsIntM β.val → IsIntM (β⁻¹).val →
  ∀ R : Finset (Formalism.MainNotions.StandardLatticesGL3.GA D a), (∀ r ∈ R, r ∈ intG D a) → (∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) →
  ∀ z : Formalism.MainNotions.StandardLatticesGL3.GA D a → Matrix (Fin d) (Fin a) D.host.E, (∀ r ∈ R, IsIntE (z r) ∧ Approx 𝔪 0 r (z r)) →
  (fun w => starRingEnd ℂ (stdFst ν e 𝔪 S T β 1 w)) =
    starRingEnd ℂ (unitChar ν e β.val) • ∑ r ∈ R, unitChar ν e (matE r) • cosInd e 𝔪 hS hT (z r) := by
  first | exact @GlobalTheory.StdExpand.conj_stdFst_eq_sum | exact GlobalTheory.StdExpand.conj_stdFst_eq_sum | (intros; apply GlobalTheory.StdExpand.conj_stdFst_eq_sum <;> assumption)
