module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSuppVecLocEq
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Formalism.LocalToGlobal.HilbertRowConditions.IsHilbertCF
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
noncomputable section

namespace GlobalTheory.LineAtG



theorem mem_latLoc_line_iff {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (L : GlobalTheory.FinPl.Lat V) (hL : L.FG) (v : GlobalTheory.FinPl.Pl D) (t : GA D V)
    (ε : Fin V.rank → D.host.E) (y : AE D) (hy : y ∈ GlobalTheory.FinPl.idAt D (· = v)) :
    Matrix.mulVec ((GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig V.gram
        (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v t))⁻¹).val
        (GlobalTheory.AdelicU.vecLoc v (finPart D ∘ fun _ : Fin 1 => y) 0 • fun i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) ⊗ₜ[D.host.F] ε i) ∈
        GlobalTheory.AdelicU.latLoc D.host.F L v ↔
      Matrix.mulVec (Formalism.L2.Theta.mt V t⁻¹) (fun i => y * Formalism.L2.Theta.incA D (ε i)) ∈ GlobalTheory.FinPl.latV V L (· = v) := by
  have hy' : ∀ i, (fun i => y * Formalism.L2.Theta.incA D (ε i)) i ∈ GlobalTheory.FinPl.idAt D (· = v) := fun i => Ideal.mul_mem_right _ _ hy
  rw [GlobalTheory.StMoves.mem_latV_iff_latLoc V L hL v _ (GlobalTheory.FinPl.KOpen.supp_mulVec V _ t⁻¹ hy'), GlobalTheory.FinPl.KOpen.fin_mulVec,
    GlobalTheory.AdelicU.vecLoc_mulVec, map_inv, map_inv]
  have hv : GlobalTheory.AdelicU.vecLoc v (finPart D ∘ fun i => y * Formalism.L2.Theta.incA D (ε i)) =
      GlobalTheory.AdelicU.vecLoc v (finPart D ∘ fun _ : Fin 1 => y) 0 • fun i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) ⊗ₜ[D.host.F] ε i := by
    funext i
    simp only [Function.comp, GlobalTheory.AdelicU.vecLoc, Pi.smul_apply, smul_eq_mul, map_mul]
    congr 1
  rw [hv]


end GlobalTheory.LineAtG
