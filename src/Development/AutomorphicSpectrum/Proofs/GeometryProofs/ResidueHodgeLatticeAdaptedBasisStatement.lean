module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ResidueHodgeLatticeAdaptedBasis
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem _root_.GlobalTheory.T.residue_hodge_lattice_adapted_basis : ∀ (E : Type) [Field E] [NumberField E] (C A : Type) [Field C] [CharZero C] [CommRing A] [Algebra A C]
    (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C) (g p q : ℕ) (ρC : 𝓞 E →+* Module.End C (Fin g → C))
    (ρHC : 𝓞 E →+* Module.End C ((Fin g → C) × Module.Dual C (Fin g → C)))
    (HV : Submodule A ((Fin g → C) × Module.Dual C (Fin g → C)))
    (tC : Fin (p + q) → (Fin g → C) × Module.Dual C (Fin g → C)) (b₁ v : Fin p → Fin g → C) (b₂ w : Fin q → Fin g → C)
    (u : Fin (p + q) → (Fin g → C) × Module.Dual C (Fin g → C)) (Ap : Matrix (Fin (p + q)) (Fin (p + q)) C)
    (P : Matrix (Fin p) (Fin p) C) (Q : Matrix (Fin q) (Fin q) C) (gm : C),
    (∀ a y, (ρHC a y).1 = ρC a y.1) → (∀ a f, ρHC a (0, f) = (0, f ∘ₗ ρC (bar a))) →
    (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) →
    (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A C).range) → HT.IsFreeOn ρHC HV tC →
    IsAdapted ρHC σ b₁ b₂ u → (∀ i, v i = ∑ k, P i k • b₁ k) → (∀ i, w i = ∑ k, Q i k • b₂ k) →
    LinearIndependent C b₁ → (∀ i, HT.eigProj ρHC σ (tC i) = ∑ k, Ap i k • u k) →
    (∀ (v' : Fin p → Fin g → C) (w' : Fin q → Fin g → C)
      (u' : Fin (p + q) → (Fin g → C) × Module.Dual C (Fin g → C)) (B : Matrix (Fin (p + q)) (Fin (p + q)) C),
      LinearIndependent C v' → Submodule.span A (Set.range v') = HT.eigSub ρC σ (stdLat A C g) →
      LinearIndependent C w' → Submodule.span A (Set.range w') = HT.eigSub ρC σ' (stdLat A C g) →
      IsAdapted ρHC σ v' w' u' → LinearIndependent C (fun i => ∑ k, B i k • u' k) →
      Submodule.span A (Set.range fun i => ∑ k, B i k • u' k) = HT.eigQuot ρHC σ HV →
      ∃ ε : Aˣ, B.det = algebraMap A C ε * gm) →
    LinearIndependent C v → Submodule.span C (Set.range v) = HT.eigSp ρC σ →
    Submodule.span A (Set.range v) = HT.eigSub ρC σ (stdLat A C g) →
    LinearIndependent C w → Submodule.span C (Set.range w) = HT.eigSp ρC σ' →
    Submodule.span A (Set.range w) = HT.eigSub ρC σ' (stdLat A C g) →
    ∃ ε : Aˣ, Ap.det * Q.det = algebraMap A C ε * gm * P.det := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.det_evaluated_frame | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.det_evaluated_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.det_evaluated_frame <;> assumption)
