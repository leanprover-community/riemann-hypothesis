module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RatFinPart

theorem exists_gq_mul_infU (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) :
    ∀ γ ∈ ratU L n, ∃ (γQ : GQ L n) (γ₀ : GL (Fin n) L), γ.1 = ratGL L n γ₀ ∧
      (((γQ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom ∧
      γ * (F.j γQ)⁻¹ ∈ infU L n := by
  intro γ hγ
  obtain ⟨γ₀, hγ₀⟩ := (Subgroup.mem_subgroupOf).1 hγ
  set σ : L →+* L := (IsCMField.complexConj L : L →+* L) with hσ
  have hU := γ.2
  change Formalism.UG.cT (conjAd L) ((γ.1 : GL (Fin n) (Ad L)) : Matrix (Fin n) (Fin n) (Ad L)) * 1 *
    ((γ.1 : GL (Fin n) (Ad L)) : Matrix (Fin n) (Fin n) (Ad L)) = 1 at hU
  rw [← hγ₀] at hU
  have h2 : Matrix.transpose ((γ₀ : Matrix (Fin n) (Fin n) L).map σ) * (γ₀ : Matrix (Fin n) (Fin n) L) = 1 := by
    have hinj : Function.Injective (algebraMap L (Ad L)) := fun x y h => by
      obtain ⟨w⟩ : Nonempty (InfinitePlace L) := inferInstance
      have := congrArg (fun z => pInf L z w) h
      simp only [pInf_algebraMap] at this
      exact w.embedding.injective this
    apply Matrix.map_injective hinj
    dsimp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), ← hU, Matrix.mul_one]
    congr 1
    ext i j
    simp [Formalism.UG.cT, ratGL, conjAd_algebraMap, hσ]
  have hu : (γ₀ : Matrix (Fin n) (Fin n) L) * conjT σ γ₀ = 1 := mul_eq_one_comm.1 h2
  let g : GL (Fin n) (AL L) := Matrix.GeneralLinearGroup.map Algebra.TensorProduct.includeLeftRingHom γ₀
  have hcj : ∀ x : L, conjAL L (x ⊗ₜ[maximalRealSubfield L] (1 : AFplus L)) =
      σ x ⊗ₜ[maximalRealSubfield L] (1 : AFplus L) := fun x => rfl
  have hg : g ∈ ReciprocityTheory.Aut.GA L n := by
    change (g : Matrix (Fin n) (Fin n) (AL L)) * conjT (conjAL L) (g : Matrix (Fin n) (Fin n) (AL L)) = 1
    have e : conjT (conjAL L) (g : Matrix (Fin n) (Fin n) (AL L)) =
        (conjT σ (γ₀ : Matrix (Fin n) (Fin n) L)).map Algebra.TensorProduct.includeLeftRingHom := by
      ext i j
      simp [conjT, g, hcj]
    rw [e]
    change (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom * _ = 1
    rw [← Matrix.map_mul, hu, Matrix.map_one _ (map_zero _) (map_one _)]
  have hq : (⟨g, hg⟩ : ReciprocityTheory.Aut.GA L n) ∈ GQ L n := by
    rw [GQ, Subgroup.mem_subgroupOf]
    exact ⟨γ₀, hu, rfl⟩
  let x : GAf L n := ⟨g, hg⟩
  refine ⟨⟨x, hq⟩, γ₀, hγ₀.symm, rfl, ?_⟩
  rw [infU, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]
  ext s t : 2
  refine FiniteAdeleRing.ext _ fun w => ?_
  have hl := F.loc x w s t
  have e1 : (cLoc w (F.j x) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) s t =
      pFin L (((F.j x).1 : Matrix (Fin n) (Fin n) (Ad L)) s t) w := rfl
  change pFin L ((γ.1 : Matrix (Fin n) (Fin n) (Ad L)) s t) w =
    pFin L (((F.j x).1 : Matrix (Fin n) (Fin n) (Ad L)) s t) w
  rw [← e1, hl, ← hγ₀]
  change pFin L (algebraMap L (Ad L) ((γ₀ : Matrix (Fin n) (Fin n) L) s t)) w =
    F.κ ((γ₀ : Matrix (Fin n) (Fin n) L) s t ⊗ₜ 1) w
  rw [F.left]
  rfl

end GlobalTheory.RatFinPart
