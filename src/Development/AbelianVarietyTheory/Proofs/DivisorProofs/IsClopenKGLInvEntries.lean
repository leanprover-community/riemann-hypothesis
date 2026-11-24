module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.AltSum

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix GroundTheory.Automorphic UpperTheory.V.Af
open GlobalTheory.CuspRep (GA Af Ad pFin pLoc)

namespace GlobalTheory.HenQ.Basic

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem mem_KGL_iff (w : HeightOneSpectrum (𝓞 K)) (y : GL (Fin n) (w.adicCompletion K)) :
    y ∈ GlobalTheory.LFun.KGL w (n := n) ↔ (∀ i j, y.val i j ∈ Formalism.UG.Ov K w) ∧ ∀ i j, (y⁻¹).val i j ∈ Formalism.UG.Ov K w := by
  rw [GlobalTheory.LFun.KGL, Formalism.UG.GLint, MonoidHom.mem_range]
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨fun i j => (z.val i j).2, fun i j => ?_⟩
    rw [← map_inv]
    exact ((z⁻¹).val i j).2
  · rintro ⟨h1, h2⟩
    let M : Matrix (Fin n) (Fin n) (Formalism.UG.Ov K w) := Matrix.of fun i j => ⟨_, h1 i j⟩
    let N : Matrix (Fin n) (Fin n) (Formalism.UG.Ov K w) := Matrix.of fun i j => ⟨_, h2 i j⟩
    have hM : M.map (Formalism.UG.Ov K w).subtype = y.val := by ext i j; rfl
    have hN : N.map (Formalism.UG.Ov K w).subtype = (y⁻¹).val := by ext i j; rfl
    have inj : Function.Injective (fun A : Matrix (Fin n) (Fin n) (Formalism.UG.Ov K w) => A.map (Formalism.UG.Ov K w).subtype) :=
      Matrix.map_injective Subtype.val_injective
    refine ⟨⟨M, N, inj ?_, inj ?_⟩, Units.ext ?_⟩
    · simp only
      rw [Matrix.map_mul, hM, hN, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    · simp only
      rw [Matrix.map_mul, hM, hN, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    · exact hM

end GlobalTheory.HenQ.Basic
