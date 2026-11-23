module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RegularSequenceGermsRegularLocal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK

theorem _root_.GlobalTheory.T.regular_sequence_germs_regular_local : ∀ (Y : Scheme.{0}) (U : Y.affineOpens) (y : Y) (hy : y ∈ U.1), IsRegularLocalRing (Y.presheaf.stalk y) → ∀ (m : ℕ) (f : Fin m → Γ(Y, U.1)), FinalTheorems.Rsp (Y.presheaf.stalk y) m (fun i => Y.presheaf.germ U.1 y hy (f i)) → IsRegularLocalRing (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal) ∧ FinalTheorems.Rsp (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal) m (fun i => algebraMap Γ(Y, U.1) _ (f i)) ∧ ∀ s : Γ(Y, U.1), y ∈ Y.basicOpen s ↔ s ∉ (U.2.primeIdealOf ⟨y, hy⟩).asIdeal := by
  first | exact @GlobalTheory.CompanionTheory.ResKCoords.stalk_to_localization | exact GlobalTheory.CompanionTheory.ResKCoords.stalk_to_localization | (intros; apply GlobalTheory.CompanionTheory.ResKCoords.stalk_to_localization <;> assumption)
