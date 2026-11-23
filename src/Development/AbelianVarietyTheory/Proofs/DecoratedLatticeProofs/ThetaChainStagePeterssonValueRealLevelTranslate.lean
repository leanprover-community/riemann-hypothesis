module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicitySpaceEquivariantRealPointsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.PetCoef

theorem pet_smul_left {D : D7} (s : PiLocalization₂ D) (a : ℂ) (f g : GA D s.V → ℂ) :
    s.pet (a • f) g = a * s.pet f g := by
  unfold PiLocalization₂.pet Lift.pet
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact MeasureTheory.integral_const_mul a _

theorem petco : ∀ D : D7, ForStage D fun c _ s => ∀ ipD ip, IsMet c s ipD ip → ∀ (u : s.CC c) (v : s.M.Vec) (b : GinfC s.V), ∀ κ ∈ Lev.levG s.V s.β s.L, s.pet (rTr s.V ((b : GA D s.V) * κ) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v))) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) = Lev.levChi s.V s.β s.L κ * ip u u * ∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ := by
  intro D c hc j hj s hs ipD ip hM u v b κ hκ
  have hmem := (mem_multT c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))).1 u.2
  have hmap := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hmem
  obtain ⟨w, hw, hU⟩ := GlobalTheory.T.multiplicitySpace_equivariant_real_points D c.θ s.V s.par s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) hc.inf v b
  have hUw := hU _ hmem
  have ev : ∀ x : s.M.Vec, PiLocalization₂.val u (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) x := by
    intro x; simp [PiLocalization₂.val, PiTensorProduct.lift_symm]
  have key : rTr s.V ((b : GA D s.V) * κ) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) =
      Lev.levChi s.V s.β s.L κ • PiLocalization₂.val u (PiTensorProduct.tprod ℂ w) := by
    funext g
    rw [ev, ev, hUw]
    simp only [rTr, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc]
    exact hmap.lev v κ hκ (g * (b : GA D s.V))
  have hsch : s.pet (PiLocalization₂.val u (PiTensorProduct.tprod ℂ w)) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) =
      ip u u * ipD (PiTensorProduct.tprod ℂ w) (PiTensorProduct.tprod ℂ v) := hM.schur u u _ _
  rw [key, pet_smul_left, hsch, hM.pure w v]
  simp only [hw, mul_assoc]

end GlobalTheory.ChainOnto.PetCoef
