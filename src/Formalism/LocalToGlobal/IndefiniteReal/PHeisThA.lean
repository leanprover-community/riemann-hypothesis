module

public import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Heis
  IsDedekindDomain NumberField Formalism.IndefR.PHeisFC
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.PHeisTh

section Tens

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]

theorem repr_snd (z : AF F ⊗[F] E) (k : Fin (Module.finrank F E)) :
    (Algebra.TensorProduct.basis (Af F) (Module.finBasis F E)).repr
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) k = (cE F E z k).2 := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, Finsupp.zero_apply]; rfl
  | tmul a e =>
    show _ = ((bA F E).equivFun (a ⊗ₜ[F] e) k).2
    rw [Algebra.TensorProduct.map_tmul, Module.Basis.equivFun_apply, Algebra.TensorProduct.basis_repr_tmul,
      Algebra.TensorProduct.basis_repr_tmul]
    simp [sndA]
    rfl
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy, Pi.add_apply]; rfl

theorem repr_fst (z : AF F ⊗[F] E) (k : Fin (Module.finrank F E)) :
    (Algebra.TensorProduct.basis (Ainf F) (Module.finBasis F E)).repr
      (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) k = (cE F E z k).1 := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, Finsupp.zero_apply]; rfl
  | tmul a e =>
    show _ = ((bA F E).equivFun (a ⊗ₜ[F] e) k).1
    rw [Algebra.TensorProduct.map_tmul, Module.Basis.equivFun_apply, Algebra.TensorProduct.basis_repr_tmul,
      Algebra.TensorProduct.basis_repr_tmul]
    simp [fstA]
    rfl
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy, Pi.add_apply]; rfl

theorem trace_tmul (e : E) :
    Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = algebraMap F (AF F) (Algebra.trace F E e) := by
  have h : Algebra.lmul (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) =
      (Algebra.lmul F E e).baseChange (AF F) := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a m => simp [LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  rw [Algebra.trace_apply, h, LinearMap.trace_baseChange]
  rfl

end Tens

section Sympl

variable {D : D7}

theorem cA_algebraMap (c : AF D.host.F) :
    cA D (algebraMap (AF D.host.F) (AE D) c) = algebraMap (AF D.host.F) (AE D) c := by
  show (Algebra.TensorProduct.map (AlgHom.id D.host.F (AF D.host.F)) D.sp.cm.sig) (c ⊗ₜ[D.host.F] (1 : D.host.E)) =
    c ⊗ₜ[D.host.F] (1 : D.host.E)
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem cA_smul (c : AF D.host.F) (z : AE D) : cA D (c • z) = c • cA D z := by
  rw [Algebra.smul_def, map_mul, cA_algebraMap, ← Algebra.smul_def]

end Sympl

end Formalism.IndefR.PHeisTh

end
