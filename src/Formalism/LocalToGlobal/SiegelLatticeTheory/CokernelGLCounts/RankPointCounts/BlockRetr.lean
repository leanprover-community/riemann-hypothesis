module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IdxRatioMap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ToCellSurj
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsUpUniMul
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEGen

@[expose] public section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D)

def UP : Subgroup (GG p) where
  carrier := {x | IsLoUni ((x.1 : GLp p) : MP p) ∧ IsUpUni ((x.2.unop : GLp p) : MP p)}
  one_mem' := ⟨ZsVolGrp.isLoUni_one, ZsVolGrp.isUpUni_one⟩
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨?_, ?_⟩
    · show IsLoUni ((x.1 * y.1 : GLp p) : MP p)
      rw [Units.val_mul]; exact _root_.PI.TermAttrConst.UnitaryGroupMassFormula.isLoUni_mul hx1 hy1
    · show IsUpUni (((x.2 * y.2).unop : GLp p) : MP p)
      rw [MulOpposite.unop_mul, Units.val_mul]; exact _root_.GlobalTheory.UpperUnipotentProductInertiaEigenvalues.isUpUni_mul hy2 hx2
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨?_, ?_⟩
    · show IsLoUni ((x.1⁻¹ : GLp p) : MP p)
      rw [Matrix.coe_units_inv]; exact (ZsVolGrp.isLoUni_inv hx1).1
    · show IsUpUni (((x.2⁻¹).unop : GLp p) : MP p)
      rw [MulOpposite.unop_inv, Matrix.coe_units_inv]; exact (ZsVolGrp.isUpUni_inv hx2).1

instance actGG : MulAction (GG p) (MP p) where
  smul x X := ((x.1 : GLp p) : MP p) * X * ((x.2.unop : GLp p) : MP p)
  one_smul X := by show ((1 : GLp p) : MP p) * X * (((1 : (GLp p)ᵐᵒᵖ).unop : GLp p) : MP p) = X; simp
  mul_smul x y X := by
    show (((x * y).1 : GLp p) : MP p) * X * ((((x * y).2).unop : GLp p) : MP p) =
      ((x.1 : GLp p) : MP p) * (((y.1 : GLp p) : MP p) * X * ((y.2.unop : GLp p) : MP p)) * ((x.2.unop : GLp p) : MP p)
    simp only [Prod.fst_mul, Prod.snd_mul, MulOpposite.unop_mul, Units.val_mul, Matrix.mul_assoc]

theorem smul_def (x : GG p) (X : MP p) : x • X = ((x.1 : GLp p) : MP p) * X * ((x.2.unop : GLp p) : MP p) := rfl

def KU : Subgroup (UP p) := (KP M p).subgroupOf (UP p)

def Va (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) : Set (MP p) :=
  {v | IsLoUni v ∧ ∀ i j : Fin (D.R.rS + 1), i ≠ j → Loc.sameBlock a.blocks i j = true → v i j = 0}

def BlockRetr (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) : Prop :=
  ∃ π : UP p →* UP p,
    CountAb.Data (a.mat) (MulAction.stabilizer (UP p) a.mat) π.ker (KU M p) π ∧
    ∀ x : UP p, π x = 1 ↔ ((x : GG p).1 : GLp p).val ∈ Va p a

end Formalism.L2.SG.Pf.CountAt
