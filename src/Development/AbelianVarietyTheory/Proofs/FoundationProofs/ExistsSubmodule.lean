module

public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemISupInfWeightSubmoduleOfDiagonalStableStatement
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
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData

@[expose] public section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.GKSubmodule

noncomputable def resAct {p q : ℕ} (M : GKMod p q) (N : Submodule ℂ M.V)
    (h : ∀ Z, ∀ x ∈ N, M.act Z x ∈ N) : Mat p q →ₗ[ℂ] Module.End ℂ N where
  toFun Z := (M.act Z).restrict (h Z)
  map_add' X Y := by
    ext x
    simp [LinearMap.restrict_apply]
  map_smul' c X := by
    ext x
    simp [LinearMap.restrict_apply]

theorem resAct_coe {p q : ℕ} (M : GKMod p q) (N : Submodule ℂ M.V)
    (h : ∀ Z, ∀ x ∈ N, M.act Z x ∈ N) (Z : Mat p q) (x : N) :
    ((resAct M N h Z x : N) : M.V) = M.act Z x := rfl

theorem exists_submodule : ∀ (p q : ℕ) (M : GKMod p q) (N : Submodule ℂ M.V), (∀ Z, ∀ x ∈ N, M.act Z x ∈ N) → ∃ (M' : GKMod p q) (i : M'.V →ₗ[ℂ] M.V), Function.Injective i ∧ LinearMap.range i = N ∧ ∀ Z x, i (M'.act Z x) = M.act Z (i x) := by
  intro p q M N h
  have hlie : IsLieAct (resAct M N h) := by
    intro X Y
    ext x
    have := congrArg (fun f : Module.End ℂ M.V => f x) (M.lie X Y)
    simpa [resAct_coe] using this
  have hk : ∀ v : N, ∃ W : Submodule ℂ N, FiniteDimensional ℂ W ∧ v ∈ W ∧
      KStable (resAct M N h) W := by
    intro v
    obtain ⟨W, hW, hv, hs⟩ := M.kfin v
    refine ⟨W.comap N.subtype, ?_, hv, ?_⟩
    · exact Module.Finite.of_injective
        (N.subtype.restrict (p := W.comap N.subtype) (q := W) (fun x hx => hx))
        (fun a b hab => Subtype.ext (Subtype.ext (congrArg (fun z : W => (z : M.V)) hab)))
    · intro X hX w hw
      exact hs X hX w hw
  have hw : ∀ v : N, v ∈ ⨆ μ : Ix p q → ℚ, wtSub (resAct M N h) μ := by
    intro v
    have h1 := GlobalTheory.T.mem_iSup_inf_weightSubmodule_of_diagonal_stable p q M.V M.act N (fun a => h _) v v.2 (M.wts v)
    have h2 : (⨆ μ : Ix p q → ℚ, N ⊓ wtSub M.act μ) ≤
        (⨆ μ : Ix p q → ℚ, wtSub (resAct M N h) μ).map N.subtype := by
      refine iSup_le fun μ x hx => ?_
      refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
      refine Submodule.mem_iSup_of_mem μ ?_
      have hx2 := hx.2
      simp only [wtSub, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker] at hx2 ⊢
      intro a
      apply Subtype.ext
      simpa [resAct_coe] using hx2 a
    obtain ⟨y, hy, hyv⟩ := h2 h1
    have : y = v := Subtype.ext hyv
    exact this ▸ hy
  exact ⟨{ V := N, act := resAct M N h, lie := hlie, kfin := hk, wts := hw }, N.subtype,
    N.injective_subtype, N.range_subtype, fun _ _ => rfl⟩

end GlobalTheory.GKSubmodule
