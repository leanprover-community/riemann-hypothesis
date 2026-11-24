module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackPureNorm
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.cm_pack_pure_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (x : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (hx : IsPure hP x) (τ : E →+* ℂ) (ℓ : Nat.Primes) (j : X.K →+* ℂ_[ℓ]) (v : Vecs X.y D.p) (w : Vecs X.y D.q), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → IsLocBasis (𝓞 E) ℓ x → X.IsCMFrame τ hx v w → ∃ (V : Subring X.K) (_ : IsDiscreteValuationRing V) (_ : IsFractionRing V X.K) (T : SAB H (Sp V)) (m'' : SABMap X.t T (spMap (algebraMap V X.K))) (δ δ' : X.K) (v' : Vecs X.y D.p) (w' : Vecs X.y D.q), (∀ a : X.K, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap V X.K).range) ∧ δ ≠ 0 ∧ δ' ≠ 0 ∧ Real.log ‖j δ‖ = logIdeal ((j.comp (X.β.comp (tauE c τ))).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j (X.β (tauE c τ (H.rt : E)))‖ ∧ Real.log ‖j δ'‖ = Real.log ‖j δ‖ ∧ (∀ a, IsComb ((δ • (1 : Matrix (Fin D.p) (Fin D.p) X.K)) a) v (v' a)) ∧ (∀ a, IsComb ((δ' • (1 : Matrix (Fin D.q) (Fin D.q) X.K)) a) w (w' a)) ∧ IsFramed (Set.range X.y) τ X.β X.y v' w' ∧ IsIntFrame X.m m'' (X.β.comp (tauIn c τ)) v' ∧ IsIntFrame X.m m'' (X.β.comp (tauIn c (ComplexEmbedding.conjugate τ))) w' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.GFin.intFrames_fin | exact GlobalTheory.CompanionTheory.Ar.Fl.GFin.intFrames_fin | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.GFin.intFrames_fin <;> assumption)
