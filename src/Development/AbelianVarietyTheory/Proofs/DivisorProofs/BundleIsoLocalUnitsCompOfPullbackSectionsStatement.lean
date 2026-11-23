module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BundleIsoLocalUnitsCompOfPullbackSections
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
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.bundleIso_local_units_comp_of_pullback_sections : ∀ (X Y' Y : Scheme.{0}) (b' : Y' ⟶ X) (β : Y ⟶ Y') (b : Y ⟶ X), β ≫ b' = b → ∀ (A : LB X) (H' : LB Y') (H : LB Y) (w' : LB.Iso H' (A.pull b')) (v : LB.Iso H (H'.pull β)) (w : LB.Iso H (A.pull b)) (ι : Type) (s : ι → LB.Sec A) (s' : ι → LB.Sec H') (s'' : ι → LB.Sec H), (∀ j, Rel b' w' (s j) (s' j)) → (∀ j, Rel β v (s' j) (s'' j)) → (∀ j, Rel b w (s j) (s'' j)) → (⨆ j, nonzeroLocus (s'' j) = ⊤) → ∀ z k k' k'', b z ∈ A.U k → β z ∈ H'.U k' → z ∈ H.U k'' → Geo.Tor.gw w (𝟙 _) z k k'' = Geo.Tor.gw w' β z k k' * Geo.Tor.gw v (𝟙 _) z k' k'' := by
  first | exact @GlobalTheory.FormalAlg.gw_comp_of_rel | exact GlobalTheory.FormalAlg.gw_comp_of_rel | (intros; apply GlobalTheory.FormalAlg.gw_comp_of_rel <;> assumption)
