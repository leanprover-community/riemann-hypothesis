module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SortSign
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SchemeCechComparisonNaturalRefinement
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.scheme_cechComparison_natural_refinement : ∀ (X X' : Scheme.{0}) (R : Type) [CommRing R] [Algebra R Γ(X, ⊤)] [Algebra R Γ(X', ⊤)] (f : X' ⟶ X) (hσ : ∀ r, f.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap R Γ(X', ⊤) ((RingHom.id R) r)) (F : X.Modules) (G : X'.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ (Scheme.Modules.pushforward f).obj G) (ι κ : Type) [LinearOrder ι] [Fintype ι] [LinearOrder κ] [Fintype κ] (U : ι → X.Opens) (U' : κ → X'.Opens) (hc : ⨆ i, U i = ⊤) (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) (hc' : ⨆ i, U' i = ⊤) (hU' : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U' i)) (τ : κ → ι), (∀ k, U' k ≤ f ⁻¹ᵁ U (τ k)) → ∀ (n : ℕ) (x : LinearMap.ker (Cube.d (cechCube R F ⊤ U) (n + 1))) (x' : LinearMap.ker (Cube.d (cechCube R G ⊤ U') (n + 1))), (∀ (t : {t : Finset κ // t.card = n + 1}) (s : {s : Finset ι // s.card = n + 1}) (h : cechOpen ⊤ U' t.1 ≤ f ⁻¹ᵁ cechOpen ⊤ U s.1), Set.InjOn τ (t.1 : Set κ) → s.1 = t.1.image τ → x'.1 t = sortSign τ t.1 • sectionsOn.res R G h (sectionsOn.map R φ (cechOpen ⊤ U s.1) (x.1 s))) → (∀ t : {t : Finset κ // t.card = n + 1}, ¬ Set.InjOn τ (t.1 : Set κ) → x'.1 t = 0) → cechHEquivCoh R hc' hU' G n (cechClass (cechCube R G ⊤ U') n x') = cohOn.pull hσ φ (le_top : (⊤ : X'.Opens) ≤ f ⁻¹ᵁ ⊤) n (cechHEquivCoh R hc hU F n (cechClass (cechCube R F ⊤ U) n x)) := by
  first | (exact @GlobalTheory.cechHEquivCoh_pull) | (exact GlobalTheory.cechHEquivCoh_pull) | (intros; apply GlobalTheory.cechHEquivCoh_pull  <;> assumption)
