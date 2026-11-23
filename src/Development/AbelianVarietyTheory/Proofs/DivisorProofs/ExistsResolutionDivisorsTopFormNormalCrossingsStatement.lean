module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResolutionDivisorsTopFormNormalCrossings
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt

theorem _root_.GlobalTheory.T.exists_resolution_divisors_topForm_normalCrossings : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n)
    (G D₀ : CartierDiv X), η ≠ 0 →
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (s : Y ⟶ X) (_ : IsDominant s)
      (B : Closeds Y),
      SmoothOfRelativeDimension n (s ≫ p) ∧ IsProper s ∧ Function.Bijective (functionFieldMap s) ∧
      {v : Y | v ∈ B ∧ Order.coheight v = 1}.Finite ∧ ratPull p s n η ≠ 0 ∧
      (∀ y : Y, ∃ (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y)
        (u : Fin n → Y.functionFieldˣ), IsSncChart (s ≫ p) n B y U hy z J w u) ∧
      (∀ (y v : Y) (g : X.functionFieldˣ), v ⤳ y → Order.coheight v = 1 → v ∉ B → G.IsEqn (s y) g →
        Scheme.ord (fnPull s g : Y.functionField) v = 0) ∧
      (∀ (y v : Y) (g : X.functionFieldˣ), v ⤳ y → Order.coheight v = 1 → v ∉ B → D₀.IsEqn (s y) g →
        Scheme.ord (fnPull s g : Y.functionField) v = 0) ∧
      (∀ (v : Y) (F : DivOver (s ≫ p)), Order.coheight v = 1 → v ∉ B → F.IsAt v →
        (fun ω => @dite ℤ (∃ a, F.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (ratPull p s n η) = 0) := by
  first | exact @GlobalTheory.ResPairSupp.exists_resolution_supp | exact GlobalTheory.ResPairSupp.exists_resolution_supp | (intros; apply GlobalTheory.ResPairSupp.exists_resolution_supp <;> assumption)
