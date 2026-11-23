module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
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

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.St

theorem repF_of_rational : ∀ (D : D7) (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F), IsAdeleIso X ιA → ∀ (h : X.B.I.Gf) (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E), X.B.I.fmat h = γ₀.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) → (∀ j, γ₀ *ᵥ X.crd (qFr wt j) = ∑ i, y₀ i j • X.crd (qFr wt i)) → ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F), y.1.1 = (y₀.map X.ιE).map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) → RepF X wt ιA h y := by
  intro D X wt ιA hA h γ₀ y₀ hf hq y hy j
  have hs : ∀ i, ιA.symm (y.1.1 i j) = Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (y₀ i j) := by
    intro i
    rw [hy, RingEquiv.symm_apply_eq, Matrix.map_apply, Matrix.map_apply, hA.1]
  simp_rw [hs]
  have hl : X.B.I.fmat h *ᵥ qA X wt j =
      fun k => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ((γ₀ *ᵥ X.crd (qFr wt j)) k) := by
    rw [hf]
    funext k
    show (γ₀.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) *ᵥ
      ((Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) ∘ X.crd (qFr wt j))) k = _
    rw [← RingHom.map_mulVec]
  rw [hl, hq j]
  funext k

  simp [qA, incl, Finset.sum_apply, map_sum, Pi.smul_apply, smul_eq_mul]

end GlobalTheory.St
