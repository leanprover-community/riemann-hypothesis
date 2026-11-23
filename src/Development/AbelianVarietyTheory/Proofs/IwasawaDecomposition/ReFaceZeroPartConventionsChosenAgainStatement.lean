module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Formalism.LocalToGlobal.IndefiniteReal.WeakCharacterisationWithError
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReFaceZeroPartConventionsChosenAgain
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

theorem _root_.GlobalTheory.T.reFace_zero_part_conventions_chosen_again : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs)) (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3), Pins R F cG → Holds R F → (∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v) → ∃ kap lam err, Pins ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) cG ∧ Holds ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) ∧ ErrEq ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) ∧ kap = R.kap ∧ (∀ i t p v, R.EEp3 p ≠ ⊥ → lam i t p v = R.lam3 i t p v) ∧ ∃ (Y' : Read (A3 := A3) ((R.updS kap lam).withErr err).toRealDat (reFace F Dc Sp Zsc).lv2 X0) (Z' : ReadL ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) X0 Y'), Y'.tup = Y.tup ∧ Y'.tupT = Y.tupT ∧ HEq Y'.jA Y.jA ∧ HEq Y'.jA0 Y.jA0 ∧ HEq Y'.eMt Y.eMt ∧ HEq Y'.PY Y.PY ∧ HEq Y'.eFT Y.eFT ∧ HEq Y'.IL Y.IL ∧ HEq Y'.PW Y.PW ∧ HEq Y'.eE Y.eE ∧ HEq Y'.mj.eW Y.mj.eW ∧ HEq Z'.eRR Z.eRR ∧ HEq Z'.jW Z.jW := by
  first | exact @GlobalTheory.Mem.R3.reFace_zero_parts | exact GlobalTheory.Mem.R3.reFace_zero_parts | (intros; apply GlobalTheory.Mem.R3.reFace_zero_parts <;> assumption)
