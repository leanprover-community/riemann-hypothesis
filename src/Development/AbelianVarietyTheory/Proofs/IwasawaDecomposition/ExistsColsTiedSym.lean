module

public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsRe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermRe
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

noncomputable section

namespace GlobalTheory.Mem.SRe.ColRe

open Formalism.BasicNotions Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.SRe NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (Z : New D)



def colsRe (C : ColsTiedSym D) : ColsTiedSym (reD D Z) := (by with_unfolding_all exact ((@ColsTiedSym.mk (reD D Z) (hermRe Z C.herm) ((by with_unfolding_all exact ((fun u => formsRe Z (C.forms u)) :)))
    ((by with_unfolding_all exact (C.eV :)))
    ((by with_unfolding_all exact (C.piU :)))
    ((by with_unfolding_all exact (C.res :)))
    ((by with_unfolding_all exact (C.car0 :)))
    ((by with_unfolding_all exact (C.carC :)))
    ((by with_unfolding_all exact (C.carM :)))
    ((by with_unfolding_all exact (C.carP :)))
    ((by with_unfolding_all exact (C.lattice₂ :)))
    ((by with_unfolding_all exact (C.pr :)))
    ((by with_unfolding_all exact (C.prk :)))
    ((by with_unfolding_all exact (C.prC :)))
    ((by with_unfolding_all exact (C.z0 :)))
    ((by with_unfolding_all exact (C.ga :)))
    ((by with_unfolding_all exact (C.sp :)))
    ((by with_unfolding_all exact (C.piG :)))
    ((by with_unfolding_all exact (C.fr0 :)))
    ((by with_unfolding_all exact (C.gl_const :)))
    ((by with_unfolding_all exact (C.chi :)))
    ((by with_unfolding_all exact (C.frame_level_zero_const :)))
    ((by with_unfolding_all exact (C.frP_const :)))) :))



theorem sameF_colsRe (C : ColsTiedSym D) :
    SameForms0LevelsAndValues Z (fun u => (C.forms u).to0) (fun u => ((colsRe Z C).forms u).to0) := by
  intro u
  refine ⟨?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact ((Eq.refl (C.forms u).to0.cls0.lev) :))
  · exact (by with_unfolding_all exact ((Eq.refl (C.forms u).to0.cls0.y) :))
  · exact (by with_unfolding_all exact ((Eq.refl (C.forms u).to0.val0.eY) :))



theorem exists_colsTiedSym (D : D7) (Z : New D) (C : ColsTiedSym D) :
    ∃ C' : ColsTiedSym (reD D Z), SameForms0LevelsAndValues Z (fun u => (C.forms u).to0) (fun u => (C'.forms u).to0) :=
  ⟨colsRe Z C, sameF_colsRe Z C⟩

end GlobalTheory.Mem.SRe.ColRe

end
