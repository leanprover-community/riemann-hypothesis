module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FinCover
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.HodgeKill
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

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.DifferentialFormSections ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Onto

namespace UpperTheory.Gal.KunnethLefschetz.G

def LineEx : Prop := ∀ {Y T : Scheme.{0}} (j : T ⟶ Y) [IsClosedImmersion j],
  (∀ y : Y, ∃ (V : Y.Opens) (s : Γ(Y, V)), y ∈ V ∧ IsAffineOpen V ∧ s ∈ nonZeroDivisors Γ(Y, V) ∧ RingHom.ker (j.app V).hom = Ideal.span {s}) →
  ∃ (D : E.LineData Y) (f : ∀ {V : Scheme.{0}} (_ : V ⟶ D.Y), Γ(V, ⊤)),
    (∀ {V' V : Scheme.{0}} (g : V' ⟶ V) (a : V ⟶ D.Y), f (g ≫ a) = g.appTop.hom (f a)) ∧
    (∀ {V : Scheme.{0}} (a b : V ⟶ D.Y) (h : a ≫ D.f = b ≫ D.f), f a = (D.u a b h : Γ(V, ⊤)) * f b) ∧
    (∀ {V : Scheme.{0}} (a : V ⟶ D.Y), (∀ v : V, (a ≫ D.f) v ∉ Set.range j) → IsUnit (f a)) ∧ sSup (Pb.𝒱D D) = ⊤ ∧ Etale D.f ∧
    ∀ (V : Y.Opens) (s : Γ(Y, V)), IsAffineOpen V → s ∈ nonZeroDivisors Γ(Y, V) → RingHom.ker (j.app V).hom = Ideal.span {s} →
      ∃ σ : (V : Scheme.{0}) ⟶ D.Y, σ ≫ D.f = V.ι ∧ f σ = V.topIso.inv.hom s

def BlowOfBl : Prop := ∀ (R : Type) [CommRing R] [IsNoetherianRing R] {Z W : Sch R} (d : ℕ) [IsProper Z.hom]
  [SmoothOfRelativeDimension d Z.hom] (π : W ⟶ XX Z), IsBl π →
    ∃ D : E.LineData W.left, Etale D.f ∧ Nonempty (Blow (XX Z).hom (dg Z).left π.left D d)

def BlowBC : Prop := ∀ (K K' : Type) [CommRing K] [CommRing K'] (φ : K →+* K') {W Z Y W' Z' Y' : Scheme.{0}}
  (q : Z ⟶ Spec (CommRingCat.of K)) (i : W ⟶ Z) (π : Y ⟶ Z) (D : E.LineData Y) (d : ℕ) (q' : Z' ⟶ Spec (CommRingCat.of K'))
  (i' : W' ⟶ Z') (π' : Y' ⟶ Z') (a : Z' ⟶ Z) (b : W' ⟶ W) (c : Y' ⟶ Y),
  IsPullback a q' q (Spec.map (CommRingCat.ofHom φ)) → IsPullback b i' i a → IsPullback c π' π a →
    Nonempty (Blow q i π D d) → Nonempty (Blow q' i' π' (D.pb c) d)

def PresBC : Prop := ∀ {Y Z Y' Z' : Scheme.{0}} (π : Y ⟶ Z) (π' : Y' ⟶ Z') (a : Z' ⟶ Z) (c : Y' ⟶ Y), IsPullback c π' π a →
  ∀ (V : Z.Opens) (C : Y.Opens) (h : C ≤ π ⁻¹ᵁ V), IsAffineOpen V → IsAffineOpen C → IsAffineOpen (a ⁻¹ᵁ V) →
  ∀ (h' : c ⁻¹ᵁ C ≤ π' ⁻¹ᵁ (a ⁻¹ᵁ V)) (σ : Type) (u : σ → Γ(Y, C)) (S : Set (MvPolynomial σ Γ(Z, V))),
    Function.Surjective (MvPolynomial.eval₂Hom (π.appLE V C h).hom u) → RingHom.ker (MvPolynomial.eval₂Hom (π.appLE V C h).hom u) = Ideal.span S →
    IsAffineOpen (c ⁻¹ᵁ C) ∧ Function.Surjective (MvPolynomial.eval₂Hom (π'.appLE (a ⁻¹ᵁ V) (c ⁻¹ᵁ C) h').hom fun s => (c.app C).hom (u s)) ∧
      RingHom.ker (MvPolynomial.eval₂Hom (π'.appLE (a ⁻¹ᵁ V) (c ⁻¹ᵁ C) h').hom fun s => (c.app C).hom (u s)) =
        Ideal.span (MvPolynomial.map (a.app V).hom '' S)

def CoordBC : Prop := ∀ (K K' : Type) [CommRing K] [CommRing K'] (φ : K →+* K') {Z Z' : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of K))
  (q' : Z' ⟶ Spec (CommRingCat.of K')) (a : Z' ⟶ Z), IsPullback a q' q (Spec.map (CommRingCat.ofHom φ)) → ∀ (V : Z.Opens), IsAffineOpen V →
  ∀ (σ : Type) (x : σ → Γ(Z, V)), (MvPolynomial.eval₂Hom (Pb.strV q V) x).Etale →
    IsAffineOpen (a ⁻¹ᵁ V) ∧ (MvPolynomial.eval₂Hom (Pb.strV q' (a ⁻¹ᵁ V)) fun s => (a.app V).hom (x s)).Etale

def OKDvr : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
  IsNoetherianRing (OK l K)

def SmSst : Prop := ∀ (O : Type) [CommRing O] (ϖ : O) {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of O)) [Smooth p],
  GlobalTheory.Et.IsStrictlySemistable ϖ p

end UpperTheory.Gal.KunnethLefschetz.G
