module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalWIdent
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ScalW


open Formalism.L2.SG.Pf.unitaryCongruence in
theorem prj_selfAdjoint : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (x y : VA X.B.I),
    hA X.B.I (GlobalTheory.ScalW.prj X u x) y = hA X.B.I x (GlobalTheory.ScalW.prj X u y) := by
  intro D X u x y
  have hT : (D.mem u).A.T ≠ 0 := (D.mem u).A.T_prime.ne_zero
  have hsum : ∀ (w : VA X.B.I) (g : Fin D.R.rS → VA X.B.I), hA X.B.I w (∑ a, g a) = ∑ a, hA X.B.I w (g a) :=
    fun w g => map_sum (hL X.B.I w) g Finset.univ
  have hd : ∀ c, divN X.B.I (D.mem u).A.T c = divN X.B.I (D.mem u).A.T 1 * c := by
    intro c; unfold divN; ring
  have hs : sigA X.B.I (divN X.B.I (D.mem u).A.T 1) = divN X.B.I (D.mem u).A.T 1 := by
    have h2 := congrArg (sigA X.B.I) (gmul_divN X.B.I _ hT 1)
    rw [map_mul, map_natCast, map_one] at h2
    rw [← divN_gmul X.B.I _ hT (sigA X.B.I _), h2]
  rw [hA_symm X.B.I y]

  simp only [prj, hA_sub_right, hA_add_right, hA_smul_right, hsum, map_sub, map_add (f := _), map_sum, map_mul]
  rw [hd (hA X.B.I (zV X u) x), hd (hA X.B.I (zV X u) y), map_mul, hs]
  simp only [← hA_symm]
  rw [add_comm (∑ a, _ * hA X.B.I x (eV X a))]
  simp only [mul_comm (hA X.B.I x _)]
  ring

end GlobalTheory.ScalW
