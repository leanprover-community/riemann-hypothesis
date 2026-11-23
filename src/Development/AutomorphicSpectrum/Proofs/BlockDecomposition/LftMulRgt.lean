module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLoc

@[expose] public section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.DiracK

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [Fintype ι] [DecidableEq ι]

def lft (ι : Type) [Fintype ι] [DecidableEq ι] : Module.End ℂ V →ₐ[ℂ] Module.End ℂ (ι → V) where
  toFun T :=
    { toFun := fun x i => T (x i)
      map_add' := fun x y => by funext i; simp
      map_smul' := fun s x => by funext i; simp }
  map_one' := by ext x i; simp
  map_mul' S T := by ext x i; simp
  map_zero' := by ext x i; simp
  map_add' S T := by ext x i; simp
  commutes' s := by ext x i; simp [Module.algebraMap_end_apply]

def rgt (V : Type) [AddCommGroup V] [Module ℂ V] : Matrix ι ι ℂ →ₐ[ℂ] Module.End ℂ (ι → V) where
  toFun M :=
    { toFun := fun x i => ∑ j, M i j • x j
      map_add' := fun x y => by funext i; simp [smul_add, Finset.sum_add_distrib]
      map_smul' := fun s x => by
        funext i
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _ }
  map_one' := by
    ext x i
    simp [Matrix.one_apply]
  map_mul' M N := by
    apply LinearMap.ext
    intro x
    funext i
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum,
      smul_smul]
    exact Finset.sum_comm
  map_zero' := by ext x i; simp
  map_add' M N := by
    apply LinearMap.ext
    intro x
    funext i
    simp [add_smul, Finset.sum_add_distrib]
  commutes' s := by
    apply LinearMap.ext
    intro x
    funext i
    simp [Module.algebraMap_end_apply, Matrix.algebraMap_matrix_apply, ite_smul]

theorem lft_apply (T : Module.End ℂ V) (x : ι → V) (i : ι) : lft ι T x i = T (x i) := rfl

theorem rgt_apply (M : Matrix ι ι ℂ) (x : ι → V) (i : ι) : rgt V M x i = ∑ j, M i j • x j := rfl

theorem lft_mul_rgt (T : Module.End ℂ V) (M : Matrix ι ι ℂ) : lft ι T * rgt V M = rgt V M * lft ι T := by
  apply LinearMap.ext
  intro x
  funext i

  simp [lft_apply, rgt_apply, map_sum]

theorem yF_eq (Kf : Fin n → Fin n → Module.End ℂ V) (c : Fin n → Fin n → Matrix ι ι ℂ) (a b : Fin n) :
    yF Kf c a b = lft ι (Kf a b) + rgt V (spinM c a b) := rfl

def dirac (P : Fin n → Fin n → Module.End ℂ V) (c : Fin n → Fin n → Matrix ι ι ℂ) : Module.End ℂ (ι → V) :=
  ∑ a, ∑ b, lft ι (P a b) * rgt V (c b a)

end GlobalTheory.CompanionTheory.DiracK
