module

public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ConclusionsAtIdentity
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmHostRootNegDiscriminantNeNegSelf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NormalisedDegreeCmEigenLineEqStatement
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem lamDegSt_of_degSt : DegSt → ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → LamDegSt H (logOm E χ).re := by
  intro hD hU hL E _ _ _ H _ χ hχ _ l c hstar nΨ n' f o La ho
  obtain ⟨-, -, -, -, hΨ, h', -, -, -, tΨ, t', -, -, -, -, -, vΨ, v', -⟩ := ho
  obtain ⟨hb, -, -, ρ, hρ, h1, h2, -⟩ := labK_spec E H l c o.K₁
  exact ⟨fun k => GlobalTheory.T.normalisedDegree_cmEigenLine_eq hD hU hL E H χ hχ hstar o.K₁ o.AΨ o.oaΨ o.xΨ o.φΨg (psiSet H) o.τΨ (labK c o.K₁) ρ
      hΨ hb.1 hρ h1 tΨ k _ (vΨ k),
    fun k => GlobalTheory.T.normalisedDegree_cmEigenLine_eq hD hU hL E H χ hχ hstar o.K₁ o.A' o.oa' o.x' o.φ'g (psiSet H)ᶜ o.τ' (labK c o.K₁) (-ρ)
      h' hb.1 (by rw [neg_sq, hρ]) h2 t' k _ (v' k)⟩

end GlobalTheory.LamF
