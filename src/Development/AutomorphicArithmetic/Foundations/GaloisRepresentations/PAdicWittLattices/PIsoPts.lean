module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.IsAdmissibleIntegralBasisChangeOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
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

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.G3

private noncomputable def geomPt (X : Scheme.{0}) (x : X) : sp (AlgebraicClosure (X.residueField x)) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) (AlgebraicClosure (X.residueField x)))) ≫
    X.fromSpecResidueField x

private theorem geomPt_apply (X : Scheme.{0}) (x : X)
    (s : sp (AlgebraicClosure (X.residueField x))) : geomPt X x s = x := by
  exact Scheme.fromSpecResidueField_apply x _

private theorem surj_of_pts {Y Z : Scheme.{0}} (f : Y ⟶ Z)
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : sp Ω ⟶ Z), ∃! y : sp Ω ⟶ Y, y ≫ f = z) : Surjective f := by
  constructor
  intro z
  obtain ⟨y, hy, -⟩ := h (AlgebraicClosure (Z.residueField z)) (geomPt Z z)
  obtain ⟨s⟩ : Nonempty (sp (AlgebraicClosure (Z.residueField z))) := ⟨IsLocalRing.closedPoint _⟩
  have key : (y ≫ f) s = geomPt Z z s := by rw [hy]
  rw [Scheme.Hom.comp_apply, geomPt_apply] at key
  exact ⟨y s, key⟩

private theorem diag_surj {Y Z : Scheme.{0}} (f : Y ⟶ Z)
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : sp Ω ⟶ Z), ∃! y : sp Ω ⟶ Y, y ≫ f = z) :
    Surjective (pullback.diagonal f) := by
  constructor
  intro p
  obtain ⟨y, hy, huniq⟩ := h _ (geomPt (pullback f f) p ≫ pullback.fst f f ≫ f)
  have e1 : geomPt (pullback f f) p ≫ pullback.fst f f = geomPt (pullback f f) p ≫ pullback.snd f f := by
    rw [huniq (geomPt (pullback f f) p ≫ pullback.fst f f) (by dsimp only; rw [Category.assoc]),
      huniq (geomPt (pullback f f) p ≫ pullback.snd f f)
        (by dsimp only; rw [Category.assoc, pullback.condition])]
  have e2 : (geomPt (pullback f f) p ≫ pullback.fst f f) ≫ pullback.diagonal f = geomPt (pullback f f) p := by
    apply pullback.hom_ext
    · simp
    · simp [e1]
  obtain ⟨s⟩ : Nonempty (sp (AlgebraicClosure ((pullback f f).residueField p))) :=
    ⟨IsLocalRing.closedPoint _⟩
  have key : ((geomPt (pullback f f) p ≫ pullback.fst f f) ≫ pullback.diagonal f) s =
      geomPt (pullback f f) p s := by rw [e2]
  rw [Scheme.Hom.comp_apply, geomPt_apply] at key
  exact ⟨_, key⟩

theorem UpperTheory.Gal.G3.pIsoPts :
    IsoPts := by
  intro Y Z f _ h
  have hd : IsIso (pullback.diagonal f) :=
    (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, diag_surj f h⟩
  have : Mono f := (pullback.isIso_diagonal_iff f).1 hd
  have : IsOpenImmersion f := IsOpenImmersion.of_flat_of_mono f
  exact (isIso_iff_isOpenImmersion_and_surjective f).2 ⟨this, surj_of_pts f h⟩
