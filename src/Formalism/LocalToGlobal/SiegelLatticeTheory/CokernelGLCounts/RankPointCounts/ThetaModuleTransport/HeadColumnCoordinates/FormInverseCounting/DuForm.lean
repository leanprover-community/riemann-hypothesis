module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.ZzMinusSecondProjTranspose
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumA

@[expose] public section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

theorem map_inv_of {K L : Type} [CommRing K] [CommRing L] {n : Type} [Fintype n] [DecidableEq n]
    (f : K →+* L) (A : Matrix n n K) (hA : IsUnit A.det) : (A⁻¹).map f = (A.map f)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul A hA, Matrix.map_one f f.map_zero f.map_one]

theorem splitFirstProj_conj (x : E) : ph1 g (M.L.cj x) = ph2 g x := by
  change (g.e (M.L.cj x)).1 = (g.e x).2
  rw [g.e_cj]
  rfl

theorem splitFirstProj_algebraMap (a : F) : ph1 g (algebraMap F E a) = a := by
  change (g.e (algebraMap F E a)).1 = a
  rw [AlgEquiv.commutes]
  rfl

def gHat (g : SplitG M.L) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) : Matrix (Ix r) (Ix r) F :=
  Matrix.fromBlocks (Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then -T else 0)
    (Zh.map (ph2 g)) (Zh.map (ph1 g)).transpose
    (Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then -T' else 0)

def pM (r : ℕ) (x : F) : Matrix (Ix r) (Ix r) F := Matrix.fromBlocks 1 (-x • 1) 0 (x • 1)

theorem map_gramG (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    (gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T')).map
        (ph1 g) = (pM r (g.q : F)⁻¹).transpose * gHat g Zh T T' * pM r (g.q : F)⁻¹ := by
  simp only [gramG, gHat, pM, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.transpose_one, Matrix.transpose_zero, Matrix.transpose_smul,
    Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, Matrix.smul_mul, Matrix.mul_smul,
    add_zero, zero_add]
  congr 1 <;> ext a b <;>
    by_cases h : a = Fin.last r ∧ b = Fin.last r <;>
    simp [cor, h, splitFirstProj_conj, splitFirstProj_algebraMap, map_mul, map_add (f := _), map_neg, map_sub, Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply] <;>
    ring

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
