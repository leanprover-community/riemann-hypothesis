module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Formalism.LocalToGlobal.IndefiniteReal.WeakCharacterisationWithError
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FurtherFaceStatementsIndependentOfError
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.XEUpdSZeroLam
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

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]



theorem read_updS_keep (R : RealDat3 D A3 Ks) (F : Face3 D A3) (lam : type_of% R.lam3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (err : type_of% R.err0)
    (hX : ∀ b, (((R.updS R.kap lam).toCx3 F).data F.cr b).XE = ((R.toCx3 F).data F.cr b).XE) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) :
    ∃ (Y' : Read (A3 := A3) ((R.updS R.kap lam).withErr err).toRealDat (reFace F Dc Sp Zsc).lv2 X0) (Z' : ReadL ((R.updS R.kap lam).withErr err) (reFace F Dc Sp Zsc) X0 Y'), Y'.tup = Y.tup ∧ Y'.tupT = Y.tupT ∧ HEq Y'.jA Y.jA ∧ HEq Y'.jA0 Y.jA0 ∧ HEq Y'.eMt Y.eMt ∧ HEq Y'.PY Y.PY ∧ HEq Y'.eFT Y.eFT ∧ HEq Y'.IL Y.IL ∧ HEq Y'.PW Y.PW ∧ HEq Y'.eE Y.eE ∧ HEq Y'.mj.eW Y.mj.eW ∧ HEq Z'.eRR Z.eRR ∧ HEq Z'.jW Z.jW := by
  refine ⟨reFaceRead (R.updS R.kap lam) F Dc Sp Zsc err X0 Y,
    reFaceReadL (R.updS R.kap lam) F Dc Sp Zsc err X0 Y (scalReadL R F lam hX X0 Y Z), ?_⟩
  have fields := And.intro (Eq.refl Y.tup) <| And.intro (Eq.refl Y.tupT) <|
    And.intro (HEq.refl Y.jA) <| And.intro (HEq.refl Y.jA0) <|
    And.intro (HEq.refl Y.eMt) <| And.intro (HEq.refl Y.PY) <|
    And.intro (HEq.refl Y.eFT) <| And.intro (HEq.refl Y.IL) <|
    And.intro (HEq.refl Y.PW) <| And.intro (HEq.refl Y.eE) <|
    And.intro (HEq.refl Y.mj.eW) <| And.intro (HEq.refl Z.eRR) (HEq.refl Z.jW)
  -- Compare the fully elaborated conjunction in the kernel, which reduces the copied fields.
  run_tac
    Lean.Elab.Tactic.closeMainGoalUsing `exact fun target _ => do
      let proof ← Lean.Elab.Tactic.elabTerm (Lean.mkIdent `fields) none
      let actual ← Lean.instantiateMVars (← Lean.Meta.inferType proof)
      let target ← Lean.instantiateMVars target
      let context ← Lean.instantiateLCtxMVars (← Lean.getLCtx)
      match Lean.Kernel.isDefEq (← Lean.getEnv) context actual target with
      | .ok true => pure proof
      | .ok false => throwError "The copied fields are not definitionally equal"
      | .error err => Lean.throwKernelException err

end GlobalTheory.Mem.R3

end
