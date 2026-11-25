module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

open Matrix
namespace GlobalTheory.AdelMatLatRight


open NumberField IsDedekindDomain in
open Matrix in
theorem _root_.GlobalTheory.AdelMatLatRight.transpose_mem_latAtV {F E : Type} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (w : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) :
    ∀ γ ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y w, γᵀ ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV Y X w := by
  intro γ hγ
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV at hγ ⊢
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hai, x, hx, y, hy, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, hai, y, hy, x, hx, ?_⟩
    rw [transpose_smul]
    congr 1
    ext i j
    simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, vecMulVec_apply, mul_comm]
  | zero => simpa using zero_mem _
  | add u v _ _ hu hv => simpa [transpose_add] using add_mem hu hv
  | neg u _ hu => simpa [transpose_neg] using neg_mem hu

end GlobalTheory.AdelMatLatRight

end
