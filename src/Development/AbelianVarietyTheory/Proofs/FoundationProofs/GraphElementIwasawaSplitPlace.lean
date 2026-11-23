module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasIwasawaDecompositionDoubledSplitPlace
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.GraphHeightLattice

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice
open Formalism.UG (GLint)

namespace GlobalTheory.GraphIwSplit

theorem isHermND_dblGram {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) : IsHermND σ (dblGram finSumFinEquiv J) := by
  refine ⟨fun i j => ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective j
    simp only [dblGram, blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases a with a | a <;> rcases b with b | b <;> simp [hJ.1]
  · rw [dblGram, det_blkMat]
    exact mul_ne_zero hJ.2 (by rw [Matrix.det_neg]; exact mul_ne_zero (pow_ne_zero _ (by simp)) hJ.2)

theorem graph_iwasawa_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L] (v : HeightOneSpectrum (𝓞 F)), IsSelfDualAt σ J L v → Nonempty (E →ₐ[F] Fv F v) → ∀ g : GLoc σ J v, ∃ p : siegelH (Fv F v) σ (dblGram finSumFinEquiv J), ∃ k ∈ KFin σ (dblGram finSumFinEquiv J) L v, ioH (Fv F v) σ rfl (g, 1) = (p : GLoc σ (dblGram finSumFinEquiv J) v) * k := by
  intro F E _ _ _ _ _ σ h n J hJ L _ v hL ⟨τ⟩ g
  exact GlobalTheory.Core.Rk.IwSplit.hasIwasawa_of_algHom h rfl hJ (isHermND_dblGram σ hJ) τ L hL _

end GlobalTheory.GraphIwSplit
