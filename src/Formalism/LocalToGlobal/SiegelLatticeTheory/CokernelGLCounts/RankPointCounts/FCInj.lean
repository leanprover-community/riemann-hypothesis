module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SecondValueMul
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEGen

@[expose] public section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) {p : PlF D}
  (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (πa : UP p →* UP p)
  (hker : ∀ x : UP p, πa x = 1 ↔ ((x : GG p).1 : GLp p).val ∈ Va p a) (g : UP p)

theorem fC_inj : Function.Injective (fC M a πa hker g) := by
  intro X Y hXY
  induction X using Quotient.inductionOn with
  | h x =>
    induction Y using Quotient.inductionOn with
    | h y =>
      apply Quotient.sound
      obtain ⟨⟨l, hl, e1⟩, ⟨ρ, hρ, e2⟩⟩ := Quotient.exact hXY
      have e1' : (((y : UP p) : GG p).1 : GLp p).val = l * (((x : UP p) : GG p).1 : GLp p).val := e1
      have e2' : ((((y : UP p) : GG p).2.unop : GLp p)).val = ((((x : UP p) : GG p).2.unop : GLp p)).val * ρ := e2
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · show Formalism.MainNotions.S.TieN.IntLow (M p) ((((y : UP p) * (x : UP p)⁻¹ : UP p) : GG p).1 : GLp p).val
        rw [first_value_mul]
        have : (((((x : UP p)⁻¹ : UP p) : GG p).1 : GLp p)).val * (((x : UP p) : GG p).1 : GLp p).val = 1 := by
          rw [← first_value_mul, inv_mul_cancel]; rfl
        rw [e1', Matrix.mul_assoc]
        rw [show (((x : UP p) : GG p).1 : GLp p).val * (((((x : UP p)⁻¹ : UP p) : GG p).1 : GLp p)).val = 1 by
          rw [← first_value_mul, mul_inv_cancel]; rfl, Matrix.mul_one]
        exact hl
      · show Formalism.MainNotions.S.TieN.IntUp (M p) (((((y : UP p) * (x : UP p)⁻¹ : UP p) : GG p).2.unop : GLp p)).val
        rw [second_value_mul, e2', ← Matrix.mul_assoc]
        rw [show ((((((x : UP p)⁻¹ : UP p) : GG p).2.unop : GLp p))).val *
            ((((x : UP p) : GG p).2.unop : GLp p)).val = 1 by rw [← second_value_mul, mul_inv_cancel]; rfl, Matrix.one_mul]
        exact hρ
      · show (y : UP p) * (x : UP p)⁻¹ ∈ πa.ker
        rw [MonoidHom.mem_ker, map_mul, map_inv, MonoidHom.mem_ker.1 x.2.1, MonoidHom.mem_ker.1 y.2.1, inv_one,
          mul_one]

end Formalism.L2.SG.Pf.CountAt
