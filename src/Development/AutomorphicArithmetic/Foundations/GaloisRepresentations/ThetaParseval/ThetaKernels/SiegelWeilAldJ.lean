module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldCut
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.JHomValK
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
theorem jEx_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.JEx_k := by
  intro F E _ _ _ _ _ σ d n h Y b ε e1 e2
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (G2 σ Y) := Subgroup.instIsTopologicalGroupSubtypeMem _
  let j : G2 σ Y →* d.G := (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b).codRestrict _ (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_mem_k d h b ε e1 e2)
  have hfr : ∀ g, inFrame d.b (j g) = blk h (inFrame b g) 1 := fun g => by
    rw [inFrame_eq]
    show incM F (d.b⁻¹).1 * (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g).1 * incM F d.b.1 = _
    rw [_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_val_k]
    simp only [← Matrix.mul_assoc, incM_inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, incM_inv_mul, Matrix.mul_one]
  refine ⟨j, ?_, fun g => by rw [hfr]; exact blk_sub h _ _, fun g => by rw [hfr]; exact blk_out h _⟩
  have h1 : Continuous fun g : G2 σ Y => g.1.1 := Units.continuous_val.comp continuous_subtype_val
  have hv : Continuous fun g : G2 σ Y => (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g).1 := by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_val_k, inFrame_eq]
    exact (continuous_const.matrix_mul ((((continuous_const.matrix_mul h1).matrix_mul continuous_const).matrix_fromBlocks
      continuous_const continuous_const continuous_const).matrix_submatrix _ _)).matrix_mul continuous_const
  have hc : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h (Y := Y) b) := by
    refine Units.continuous_iff.2 ⟨hv, ?_⟩
    have e : (fun g : G2 σ Y => ((_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g)⁻¹ : GL _ _).1) = fun g : G2 σ Y => (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g⁻¹).1 :=
      funext fun g => by rw [map_inv]
    rw [e]
    exact hv.comp continuous_inv
  exact hc.subtype_mk _
end PositivityTheory.SiegelWeilFormula.Ald
end
end
