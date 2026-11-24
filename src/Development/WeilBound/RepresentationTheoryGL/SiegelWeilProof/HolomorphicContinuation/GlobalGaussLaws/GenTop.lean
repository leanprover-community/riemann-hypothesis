module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRedField
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocalL2IsometryAlt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
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

@[expose] public section

noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.AdelicU GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GenTopH

variable {D : D7} {n : ℕ}

theorem mat_projFin (g : G D n) : (mat g).map (finPart D) = (HA.mat _ D.sp.cm.sig (Jst D n) (projFin D.sp.cm.sig (Jst D n) g)).1 :=
  rfl

theorem mat_projInf (g : G D n) : (mat g).map (infPart D) = (HA.mat _ D.sp.cm.sig (Jst D n) (projInf D.sp.cm.sig (Jst D n) g)).1 :=
  rfl

end PositivityTheory.Rg.Sw.Glob.GenTopH

namespace PositivityTheory.Rg.Sw.Glob

theorem genA_of : UnitD → PIn → KInInf → KInFin → GenA := by
  intro _ hP hKi hKf D n
  show Subgroup.closure (genSet D n) = ⊤
  rw [eq_top_iff]
  intro g _
  obtain ⟨p, hp, k, hk, rfl⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D n g
  refine Subgroup.mul_mem _ (hP D n p hp) ?_
  rw [← ofInf_projInf_mul_ofFin_projFin D.sp.cm.sig (Jst D n) k]
  have hk' := mem_levelAll.1 hk
  refine Subgroup.mul_mem _ (hKi D n _ ?_ ?_) (hKf D n _ ?_ ?_)
  · refine mem_levelAll.2 ⟨fun v => ?_, fun w => ?_⟩
    · rw [proj_ofInf]; exact one_mem _
    · rw [projArch_ofInf, projInfArch_projInf]; exact hk'.2 w
  · rw [GenTopH.mat_projFin, projFin_ofInf]; rfl
  · refine mem_levelAll.2 ⟨fun v => ?_, fun w => ?_⟩
    · rw [proj_ofFin, projFinLoc_projFin]; exact hk'.1 v
    · rw [projArch_ofFin]; exact one_mem _
  · intro τ
    have e : Formalism.IndefR.Eqv.psiT D τ = (Formalism.IndefR.Eqv.thetaC D τ).comp (infPart D) := rfl
    rw [e, RingHom.coe_comp, ← Matrix.map_map, GenTopH.mat_projInf, projInf_ofFin]
    exact Matrix.map_one _ (map_zero _) (map_one _)

end PositivityTheory.Rg.Sw.Glob
