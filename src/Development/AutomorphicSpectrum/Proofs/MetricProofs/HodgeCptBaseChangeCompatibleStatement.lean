module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptBaseChangeCompatible
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

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.hodgeCpt_base_change_compatible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S y) (Z : Scheme.{0}) (ξ' : Spec (CommRingCat.of Ω') ⟶ Z) (h : Z ⟶ A.X), (∀ q : Z, genPt ξ' ⤳ q) → CoordTie ℤ ξ' (seg y') → IsNormalScheme Z → GlobalTheory.CompanionTheory.Ar.Dominates ξ' A.ξ h i → Smooth h → ∃ (A' : HodgeCpt Y S y') (e : A'.X ≅ Z) (j : A.Li →+ A'.Li), A'.ξ ≫ e.hom = ξ' ∧ HodgeOver A' A (e.hom ≫ h) i j ∧ A'.R = A.R ∧ Submodule.span Ω' (Set.range j) = ⊤ ∧ ∀ s, A'.V s = (A.V s).pull A'.ξ (e.hom ≫ h) j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HcptFlat.hodgeCpt_pull_smooth | exact GlobalTheory.CompanionTheory.Ar.HcptFlat.hodgeCpt_pull_smooth | (intros; apply GlobalTheory.CompanionTheory.Ar.HcptFlat.hodgeCpt_pull_smooth <;> assumption)
