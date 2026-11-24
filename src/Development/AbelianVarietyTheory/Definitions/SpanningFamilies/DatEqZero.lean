module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict
open scoped Classical

namespace GlobalTheory.ClsVal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} {H : Host E} {Dw : Datum H}
  {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

def clsSum (σ : c.F →+* ℂ) (X : Data E r) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ)
    (idx : Fin g ≃ X.Ψ × Fin r) (eL : LtN Dw n ≃ Harm.Var X.Ψ q0 X.p0 (Fin n)) {l₂ : Geo.Tor.Level H} {Cl : Type}
    [Fintype Cl] (w : Cl → (Fin n → LevQ Dw l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F)
    (ep : Cl → c.F) (P : Cl → MvPolynomial (LtN Dw n) c.F) (L : Lt E r) (v : TF n g)
    (Y : Cl → (Fin n → LevQ Dw l₂) → Matrix (Fin n) (Fin r) E) (x : Frame X.Ψ r) : ℂ :=
  ∑ k, σ (vol * ((gam k : c.F))⁻¹ * ep k * ((((La k).mIdx (Nc k) r : c.F))⁻¹ *
      ((Nat.card (Fin n → LevQ Dw l₂) : c.F))⁻¹ * ((La k).zCard (Nc k) r : c.F))) *
    thP X hr bas idx (gphi X bas (H.w0 : E) (La k).La L v (fun q => σ (w k q)) (Y k))
      (MvPolynomial.rename eL (MvPolynomial.map σ (P k))) x

def CvIs (d : DeltaDat Xo c n) [Algebra d.c₂.F ℂ] (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ)
    (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (L : Lt E r) (cv : (Dw.La →ₗ[𝓞 E] (Fin r → E)) → ℂ) : Prop :=
  ∀ x ∈ X.dom, ∀ (y₂ : FrPt d.Xo₂ d.c₂ ℂ) (A : AnFib X bas idx e x L y₂) (mk : Dw.La →ₗ[𝓞 E] (Fin r → E)),
    IsMark d.l₂ L mk → A.Marked mk → evR d.Xo₂ d.c₂ d.cδ y₂ = cv mk

def DatEq (d : DeltaDat Xo c n) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ)
    (w : (Fin n → LevQ Dw d.l₂) → c.F) : Prop :=
  ∀ (s : Sim Dw), s.InGam l d.l₂ → ∀ (kI : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) (σq : LevQ Dw d.l₂ ≃ LevQ Dw d.l₂),
    (∀ a : Dw.La, (Submodule.Quotient.mk (s.f d.l₂.M a) : LaI Xo c d) = kI (Submodule.Quotient.mk a)) →
    (∀ a : Dw.La, σq (Submodule.Quotient.mk a) = Submodule.Quotient.mk (s.f d.l₂.M a)) →
    ∀ q, w (fun b => σq.symm (q b)) = (((ψ kI)⁻¹ : c.Fˣ) : c.F) * w q

def LatsOK (M : ℕ) {Cl : Type} (La : Cl → GenLat E n) (Nc : Cl → ℕ) : Prop :=
  ∀ k, (La k).Unimod ∧ (La k).TrivAt M ∧ (La k).LevOK (Nc k) M

end

end GlobalTheory.ClsVal
