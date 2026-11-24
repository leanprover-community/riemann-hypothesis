module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SplitComps
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EffectiveScaledWeightOfRetraction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.effective_scaled_weight_of_retraction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (G : RefGeo Y) (A : G.An) (ν : RootIx D → ℤ) (k q' : ℕ) (s : G.Ω), (∃ inv : A.Sys.X → A.Re.R.X, ReciprocityTheory.AnForm.M.HoloMap A.Sys.A A.Re.R.A inv ∧ ∀ x, inv (A.Re.π x) = x) → SplitComps Y → 0 < k → 0 < q' → s ≠ 0 → G.IsEff (fun r => (k * q' : ℕ) * ν r) q' s → ∃ (Fx : FixedData Y A.Sys) (R : Top.RootModel (CMType H) (D.p + D.q)) (o : RootOrigin Y ∅ R Fx), genPt Fx.ξf = genPt G.𝔐.ξ₀ ∧ Fx.kA = k ∧ Fx.q' = q' ∧ (∀ r, Fx.n r = (k * q' : ℕ) * ν r) ∧ o.Fl.deg = 1 ∧ o.Re.J = ⊤ ∧ Ht.AmpleQ R.y R.A.a ∧ Cmp.IsEmbedded o.Re.R.A R.P o.Re.R.U o.Re.R.lift ∧ Function.Bijective o.Re.π ∧ (∀ x : A.Sys.X, ∃ (U : Set A.Sys.X) (lam : A.Sys.X → Fin (Fx.m + 1) → ℂ), IsOpen U ∧ x ∈ U ∧ (∀ i, A.Sys.A.HoloOn U fun y => lam y i) ∧ (∀ y ∈ U, ∃ a₀ : ℂ, a₀ ≠ 0 ∧ lam y = a₀ • Fx.pt y) ∧ ∀ p, lam x p ≠ 0 → ∀ j, x ∈ (A.Sys.A.chart j).source → (fderiv ℂ (fun z i => lam ((A.Sys.A.chart j).symm z) i / lam ((A.Sys.A.chart j).symm z) p) (A.Sys.A.chart j x)).ker = ⊥) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RefRoot.refRoot | exact GlobalTheory.CompanionTheory.Ar.RefRoot.refRoot | (intros; apply GlobalTheory.CompanionTheory.Ar.RefRoot.refRoot <;> assumption)
