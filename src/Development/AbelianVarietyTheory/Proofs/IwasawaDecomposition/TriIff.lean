module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
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

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.FlagBundle

namespace GlobalTheory.ShFam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

def EigFrame.Coord {R R' : Type} [CommRing R] [CommRing R'] {φ : c.F →+* R} {φ' : c.F →+* R'}
    {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} (f : EigFrame Z φ x) (ψ : R →+* R') (g : EigFrame Z φ' x')
    (A : Mat Dw.mult R') : Prop :=
  x' = spMap ψ ≫ x ∧ φ' = ψ.comp φ ∧
    ∀ τ i, IsCombAtG Z.t x' (fun k => spMap (Formalism.L2.Pj.dualMap ψ) ≫ f.v τ k) (A τ i) (g.v τ i)

def EigFrame.Stable {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x) : Prop :=
  ∀ (R' : Type) [CommRing R'] [IsLocalRing R'] (ψ : R →+* R'),
    ∃ g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x), ∀ τ i, g.v τ i = spMap (Formalism.L2.Pj.dualMap ψ) ≫ f.v τ i

theorem EigFrame.tri_iff {R R' : Type} [CommRing R] [CommRing R'] {φ : c.F →+* R} {φ' : c.F →+* R'}
    {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} (f : EigFrame Z φ x) (ψ : R →+* R') (g : EigFrame Z φ' x')
    (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R'ˣ) :
    f.Tri ψ g t ↔ ∃ A : Mat Dw.mult R', f.Coord ψ g A ∧ (∀ τ i, A τ i i = t τ i) ∧ ∀ τ i k, i < k → A τ i k = 0 := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    choose A hA hA' hA'' using h3
    exact ⟨A, ⟨h1, h2, hA''⟩, hA, hA'⟩
  · rintro ⟨A, ⟨h1, h2, h3⟩, hA, hA'⟩
    exact ⟨h1, h2, fun τ i => ⟨A τ i, hA τ i, hA' τ i, h3 τ i⟩⟩

variable {F : Type} [Field F]

def Tied (e : F ≃+* c.F) (Y : GlobalTheory.ProjVar.Var F) (π : Y.X ⟶ gen Z)
    (f₀ : EigFrame Z (constF e Y) (genericPt Y ≫ π ≫ genι Z)) {k : (E →+* ℂ) → ℕ} (S : Fr (ratOf Y) Dw.mult k)
    (A₀ : Mat Dw.mult Y.Fn) : Prop :=
  A₀ ∈ S.S (genericPoint Y.X) ∧ ∀ y : Y.X, ∀ A ∈ S.S y, ∃ (φ : c.F →+* Y.X.presheaf.stalk y)
    (f : EigFrame Z φ (stalkPt Y y ≫ π ≫ genι Z)),
    f.Coord (algebraMap (Y.X.presheaf.stalk y) Y.X.functionField) f₀ (A₀ * A⁻¹)

end GlobalTheory.ShFam
