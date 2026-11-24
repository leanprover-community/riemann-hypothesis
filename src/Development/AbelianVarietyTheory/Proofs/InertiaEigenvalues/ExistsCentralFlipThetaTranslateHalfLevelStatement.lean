module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.BaseIntSet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCentralFlipThetaTranslateHalfLevel
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.exists_centralFlip_thetaTranslate_halfLevel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → Odd W.rank → ∀ (χ : Formalism.L2.Host.HChar D.host.E) (M₀ l : ℕ), ChiData χW χ M₀ → l.Prime → M₀ ≠ 0 → ∃ (Z : Finset (GA D V)) (c : ℕ), (∀ z ∈ Z, z ∈ GfC V) ∧ ∀ (H : Geo.Tor.Host D.host.E) (l₂ : Geo.Tor.Level H) (pd : ℕ), l₂.M = M₀ * pd → Nat.Coprime pd M₀ → Nat.Coprime pd l → Nat.Coprime l₂.M (GlobalTheory.Tow.badN D) → ∀ (k : Type) [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) (O : Subring ℂ), ((l : ℕ) : 𝓞 k) ∈ la.asIdeal → ValRing σ la O → ConjIn D σ → χ.ValuesIn (-1 / 2) σ → zeta l₂.M ∈ O → ∀ (e e₂ : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → (∀ PP ∈ P, ((l₂.M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → IsHalfIdem l₂ e₂ → ∃ z₂ ∈ Z, ∃ z₁ ∈ GfC V, OneAt V l z₁ ∧ ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e l₂.M O, ∃ f' ∈ trSp ψ V W ΛV ΛW f₀ e₂ l₂.M O, ∀ (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (Q : MvPolynomial (FVar D W.rank V.rank) ℂ) (s : GA D V) (g : GA D W), (l : ℂ) ^ c * thetaKO om s g (stdF ψ θ V W sW BW f Q) = thetaKO om (s * z₂ * z₁) g (stdF ψ θ V W sW BW f' Q) := by
  first | exact @GlobalTheory.LevelSeries.exists_flip_theta | exact GlobalTheory.LevelSeries.exists_flip_theta | (intros; apply GlobalTheory.LevelSeries.exists_flip_theta <;> assumption)
