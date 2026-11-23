module

public import Formalism.LocalToGlobal.ProjectiveLattices.ThClass
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LevelFourierTransformAutAndHomogeneous
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GalTw

theorem _root_.GlobalTheory.T.level_fourier_transform_aut_and_homogeneous : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ), (∀ ta : c.F ≃+* c.F, (∃ a a' : ℕ, ta (zetaM c) = zetaM c ^ a ∧ a * a' ≡ 1 [MOD l.M]) ∧ ∀ a a' : ℕ, ta (zetaM c) = zetaM c ^ a → a * a' ≡ 1 [MOD l.M] → ∀ (φ : (Fin n → LevQc Dw l) → c.F) (q : Fin n → LevQ Dw l), ta (phiHat c φ q) = phiHat c (fun x => ta (φ (a' • x))) q) ∧ (∀ (u : c.F) (φ : (Fin n → LevQc Dw l) → c.F) q, phiHat c (fun x => u * φ x) q = u * phiHat c φ q) ∧ ∀ (nab : NabV Xo c) (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (b u : c.F) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S), ShortValAt Xo c nab w Λ b N P y v → ShortValAt Xo c nab (fun q => u * w q) Λ b N P y (algebraMap c.F S u * v) := by
  first | exact @GlobalTheory.GalTw.phiHat_aut_and_mul | exact GlobalTheory.GalTw.phiHat_aut_and_mul | (intros; apply GlobalTheory.GalTw.phiHat_aut_and_mul <;> assumption)
