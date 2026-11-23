module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix

namespace GlobalTheory.GLFinPlaces

theorem gl_mem_int_cofinite (E : Type) [Field E] [NumberField E] (a : ℕ) (k : GL (Fin a) (Af E)) :
    {w : HeightOneSpectrum (𝓞 E) | GeneralLinearGroup.map (pLoc E w) k ∉ KGL w (n := a)}.Finite := by
  have hent : ∀ M : Matrix (Fin a) (Fin a) (Af E), ∀ᶠ w in Filter.cofinite,
      ∀ i j, (M i j) w ∈ w.adicCompletionIntegers E := by
    intro M
    rw [Filter.eventually_all]; intro i
    rw [Filter.eventually_all]; intro j
    exact (M i j).2
  have h := (hent (k : Matrix (Fin a) (Fin a) (Af E))).and (hent ((k⁻¹ : GL (Fin a) (Af E)) : Matrix (Fin a) (Fin a) (Af E)))
  rw [Filter.eventually_cofinite] at h
  refine h.subset ?_
  intro w hw
  simp only [Set.mem_setOf_eq] at hw ⊢
  intro hg
  apply hw
  have key : ∀ M : Matrix (Fin a) (Fin a) (Af E), (∀ i j, (M i j) w ∈ w.adicCompletionIntegers E) →
      M.map (pLoc E w) ∈ (RingHom.mapMatrix (m := Fin a) (Ov E w).subtype).range := by
    intro M hM
    exact ⟨Matrix.of fun i j => (⟨(M i j) w, hM i j⟩ : Ov E w), by ext i j; rfl⟩
  refine P.glint_mem_range_of_integral _ _ ?_ ?_
  · exact key _ hg.1
  · rw [← map_inv]
    exact key _ hg.2

end GlobalTheory.GLFinPlaces
