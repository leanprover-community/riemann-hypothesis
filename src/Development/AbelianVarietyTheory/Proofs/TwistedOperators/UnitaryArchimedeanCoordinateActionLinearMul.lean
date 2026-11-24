module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchActOne
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

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap

noncomputable section

namespace GlobalTheory.ArchLine

theorem archAct_linear_mul : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W),
    (∀ (h : UA σ W.J) (v v' : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      archAct M h (v + v') = archAct M h v + archAct M h v') ∧
    (∀ (h : UA σ W.J) (c : ℝ) (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      archAct M h (c • v) = c • archAct M h v) ∧
    (∀ (h h' : UA σ W.J) (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      archAct M (h * h') v = archAct M h (archAct M h' v)) := by
  intro F E _ _ _ _ _ σ n d X W M
  refine ⟨fun h v v' => ?_, fun h c v => ?_, fun h h' v => ?_⟩
  · unfold archAct
    rw [Prod.fst_add, Prod.snd_add, lift_add, lift_add, ← Prod.mk_add_mk, map_add (f := _)]
    simp only [actAB, Matrix.mul_add, Matrix.add_mul]
    rw [coordI_add]
  · unfold archAct
    rw [Prod.smul_fst, Prod.smul_snd, lift_smul, lift_smul, ← Prod.smul_mk, map_smul]
    simp only [actAB, Matrix.mul_smul, Matrix.smul_mul]
    rw [coordI_smul]
  · unfold archAct
    rw [lift_coordI]
    simp only [actAB, Matrix.mul_smul, Matrix.smul_mul, coordI_one]
    congr 1
    simp only [one_mul, Units.val_one, Subgroup.coe_one, Subgroup.coe_mul, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    simp only [Matrix.one_mul]

end GlobalTheory.ArchLine
