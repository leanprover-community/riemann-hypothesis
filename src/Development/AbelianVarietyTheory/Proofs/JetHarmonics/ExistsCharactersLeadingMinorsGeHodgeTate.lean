module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLeadingMinorsGeOfLeRank
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem exists_chars_leading_minors_ge :
    ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (d s N : ℕ) (F : Fin d → PS O 2 d) (w : Fin s → Fin d → O), Function.Surjective (res w) → ∀ (u : Fin N → PS O 1 d), (∀ k, IsCh F (u k)) → ∀ c : O, c ≠ 0 → (∀ f : Fin d → O, c • f ∈ Submodule.span O (Set.range fun k => dl (u k))) → ∃ χ : Fin s → PS O 1 d, (∀ b, IsCh F (χ b)) ∧ ∀ i : Fin s, v (algebraMap O C c) ^ s ≤ v (algebraMap O C (Matrix.of fun a b : Fin (i.val + 1) => ∑ j, w (Fin.castLE i.isLt a) j * dl (χ (Fin.castLE i.isLt b)) j).det) := by
  intro C _ v O _ _ hv d s N F w hw u hu c hc hspan
  have hA : ∀ y : Fin s → O,
      c • y ∈ Submodule.span O (Set.range fun k => res w (dl (u k))) := by
    intro y
    obtain ⟨f, rfl⟩ := hw y
    have h1 : (Set.range fun k => res w (dl (u k))) = res w '' (Set.range fun k => dl (u k)) := by
      rw [← Set.range_comp]
      rfl
    rw [h1, ← Submodule.map_span, ← map_smul]
    exact Submodule.mem_map_of_mem (hspan f)
  obtain ⟨t, ht, hmin⟩ := GlobalTheory.exists_leading_minors_ge C v O hv s _ c hc hA
  choose k hk using ht
  refine ⟨fun b => u (k b), fun b => hu _, fun i => ?_⟩
  have hm : (Matrix.of fun a b : Fin (i.val + 1) =>
      ∑ j, w (Fin.castLE i.isLt a) j * dl (u (k (Fin.castLE i.isLt b))) j) =
      Matrix.of fun a b : Fin (i.val + 1) => t (Fin.castLE i.isLt b) (Fin.castLE i.isLt a) := by
    ext a b
    rw [Matrix.of_apply, Matrix.of_apply, ← hk]
    simp [res, Matrix.mulVec, dotProduct]
  rw [hm]
  exact (pow_le_pow_right_of_le_one' (hv.map_le_one c) i.isLt).trans (hmin i)

end GlobalTheory.CharDepth
