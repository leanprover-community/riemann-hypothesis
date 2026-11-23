module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.Cyc

theorem htBasis_of_isDec : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m d : ℕ) (M U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (Dm : Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l) (J : Set ℤ), IsDec act χ K m M Dm U g → HTBasis act χ (Gj K m) M J → HTBasis act χ (Gj K m) U J := by
  intro l _ act χ _ _ K m d M U Dm g J hD hH
  obtain ⟨hdet, -, -, -, hrel⟩ := hD
  obtain ⟨e, u, hli, hu, hfix⟩ := hH
  have hDe : ∀ v : Fin d → PadicComplex l, Dm.mulVec (Dm⁻¹.mulVec v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hinj : ∀ v w : Fin d → PadicComplex l, Dm.mulVec v = Dm.mulVec w → v = w := by
    intro v w h
    have h2 := congrArg (fun x => Dm⁻¹.mulVec x) h
    simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec] using h2
  refine ⟨fun k => Dm⁻¹.mulVec (e k), u, ?_, hu, ?_⟩
  · refine LinearIndependent.of_comp Dm.mulVecLin ?_
    have : (Dm.mulVecLin ∘ fun k => Dm⁻¹.mulVec (e k)) = e := by
      funext k
      exact hDe (e k)
    rw [this]
    exact hli
  · intro σ hσ k
    apply hinj
    have hmap : (Dm.map (act σ)).mulVec (fun a => act σ (Dm⁻¹.mulVec (e k) a)) =
        fun a => act σ (e k a) := by
      funext a
      conv_rhs => rw [← hDe (e k)]

      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
    have h1 := hfix σ hσ k
    unfold twAct at h1 ⊢
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hrel σ hσ, ← Matrix.mulVec_mulVec, hmap, h1, hDe]

end GlobalTheory.Cyc
