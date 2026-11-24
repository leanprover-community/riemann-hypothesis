module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

section Translate

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem tensCol_phiOne_charInd_smul (χ : AddChar 𝓀[k] ℂ) (P₁ : Pair k n') (Q : Pair k n) (g : GL n k)
    (x : Matrix n (n' ⊕ Fin 1) k) :
    tensCol (phiOne P₁ Q) (charInd χ Q) ((g⁻¹ : GL n k).val * x) =
      tensCol (phiOne P₁ (g • Q)) (charInd χ (g • Q)) x := by
  have hcol : (fun i => ((g⁻¹ : GL n k).val * x) i (Sum.inr 0)) = (g⁻¹ : GL n k) • (fun i => x i (Sum.inr 0)) := rfl
  have hsub : ((g⁻¹ : GL n k).val * x).submatrix id Sum.inl = (g⁻¹ : GL n k).val * x.submatrix id Sum.inl := rfl
  have hphi : ∀ z : Matrix n n' k, phiOne P₁ (g • Q) z = phiOne P₁ Q ((g⁻¹ : GL n k).val * z) := by
    intro z
    have h := phiOne_smul (P := P₁) (Q := Q) (x := z) (1 : GL n' k) g
    rw [one_smul] at h
    rw [h, Units.val_one, Matrix.mul_one]
  have hchi : ∀ y : n → k, charInd χ (g • Q) y = charInd χ Q ((g⁻¹ : GL n k) • y) := by
    intro y
    unfold charInd vecInd
    rw [Pair.smul_lat, mem_smul_iff]
    split_ifs with hy
    · have hv := Pair.hasVal_ev (P := g • Q) (x := y) (by rw [Pair.smul_lat, mem_smul_iff]; exact hy)
      rw [Pair.smul_hasVal] at hv
      rw [hv.ev_eq]
    · simp
  unfold tensCol
  rw [hsub, hcol, hphi, hchi]

end Translate

end GlobalTheory.FinPl

namespace GlobalTheory.FinPl

end GlobalTheory.FinPl
