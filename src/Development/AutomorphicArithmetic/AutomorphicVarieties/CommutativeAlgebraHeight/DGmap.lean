module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom

@[expose] public section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem gdet_inst {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (B : Type) [CommRing B]
    (i j : Algebra A B) (h : ∀ a, @algebraMap A B _ _ i a = @algebraMap A B _ _ j a) (x : MonoidAlgebra B G) :
    @GDet.D n A G _ _ D B _ i x = @GDet.D n A G _ _ D B _ j x := by
  have : i = j := Algebra.algebra_ext _ _ h
  subst this
  rfl

private theorem gdet_chi {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G)
    {B : Type} [CommRing B] (f : A →+* B) (y : MonoidAlgebra A G) :
    (D.map f).chi (MonoidAlgebra.mapRingHom G f y) = (D.chi y).map f := by
  letI : Algebra A B[X] := ((algebraMap B B[X]).comp f).toAlgebra
  let φ : A[X] →ₐ[A] B[X] :=
    { Polynomial.mapRingHom f with
      commutes' := fun a => by
        change Polynomial.map f (C a) = C (f a)
        exact Polynomial.map_C f }
  have h := D.nat A[X] B[X] φ (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y)
  refine Eq.trans ?_ h
  change D.D B[X] _ = D.D B[X] _
  congr 1
  have hφ : (φ : A[X] →+* B[X]) = Polynomial.mapRingHom f := rfl
  rw [hφ]
  ext g : 2
  simp

theorem UpperTheory.V.CA.d_gmap :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G), D.map (RingHom.id A) = D ∧ (∀ {B C : Type} [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C), (D.map f).map g = D.map (g.comp f)) ∧ (∀ {B : Type} [CommRing B] (f : A →+* B) (y : MonoidAlgebra A G), (D.map f).chi (MonoidAlgebra.mapRingHom G f y) = (D.chi y).map f ∧ ∀ i, (D.map f).lam i (MonoidAlgebra.mapRingHom G f y) = f (D.lam i y)) ∧ ∀ {B : Type} [CommRing B] (f : A →+* B) (ρ : G →* Matrix (Fin n) (Fin n) A), (GDet.ofRep ρ).map f = GDet.ofRep (f.mapMatrix.toMonoidHom.comp ρ) := by
  intro n A G _ _ D
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact GDet.ext fun B _ j x =>
      gdet_inst D B ((algebraMap A B).comp (RingHom.id A)).toAlgebra j (fun _ => rfl) x
  · intro B C _ _ f g
    exact GDet.ext fun S _ _ x => gdet_inst D S _ _ (fun _ => rfl) x
  · intro B _ f y
    refine ⟨gdet_chi D f y, fun i => ?_⟩
    simp only [GDet.lam, gdet_chi, Polynomial.coeff_map, map_mul, map_pow, map_neg, map_one]
  · intro B _ f ρ
    refine GDet.ext fun S _ _ x => ?_
    letI : Algebra A S := ((algebraMap B S).comp f).toAlgebra
    change (GDet.repAlg ρ S x).det = (GDet.repAlg (f.mapMatrix.toMonoidHom.comp ρ) S x).det
    congr 2
