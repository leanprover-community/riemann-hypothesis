module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
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
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SatakeDualWeyl.StatementE
public import Formalism.SatakeDualWeyl.StatementG

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MemLevRed

theorem mem_lev_of_reductions : ∀ {D : D7} (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (LT : LevDat D.host.E ℂ T.rank) (y : GL (Fin T.rank) (EAf D)), LT.Q = ∅ → y ∈ UA D.sp.cm T.gram → y ∈ St βT → ∀ (a b : ∀ PP : ↥LT.Pg, GL (Fin T.rank) (kP PP.1)), (∀ PP, a PP ∈ blockTri (blkOf LT.r LT.t)) → (∀ PP, b PP ∈ blockTri (blkOf LT.r LT.t)) → (fun PP => upperLeftBlock LT.hr (a PP)) ∈ LT.P.H → (fun PP => upperLeftBlock LT.hr (b PP)) ∈ LT.P.H → (∀ PP : ↥LT.Pg, b PP * redFn βT PP.1 y = a PP) → y ∈ lev D.sp.cm T.gram βT LT := by
  intro D T βT LT y hQ hU hS a b ha hb hHa hHb hab
  have hred : ∀ PP : ↥LT.Pg, redFn βT PP.1 y = (b PP)⁻¹ * a PP := fun PP => by
    rw [← hab PP, inv_mul_cancel_left]
  refine mem_lev.2 ⟨mem_parLev.2 ⟨hU, hS, fun PP hP => ?_, fun PP hP => ?_⟩, ?_⟩
  · rw [hred ⟨PP, hP⟩]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hb ⟨PP, hP⟩)) (ha ⟨PP, hP⟩)
  · rw [hQ] at hP
    exact absurd hP (Finset.notMem_empty PP)
  · have h1 : rTup βT LT y = (fun PP => upperLeftBlock LT.hr (b PP)) ⁻¹ * (fun PP => upperLeftBlock LT.hr (a PP)) := by
      funext PP
      have hb2 := blockTri_blkOf_le LT.r LT.t (hb PP)
      have ha2 := blockTri_blkOf_le LT.r LT.t (ha PP)
      show upperLeftBlock LT.hr (redFn βT PP.1 y) = (upperLeftBlock LT.hr (b PP))⁻¹ * upperLeftBlock LT.hr (a PP)
      rw [hred PP]
      unfold upperLeftBlock
      rw [extendMatrixByIdentityAlongIndices_mul _ (Subgroup.inv_mem _ hb2) ha2, extendOne_inv _ hb2]
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hHb) hHa

end GlobalTheory.MemLevRed
