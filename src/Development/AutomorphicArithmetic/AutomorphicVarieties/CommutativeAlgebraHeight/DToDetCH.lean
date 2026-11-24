module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
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

private theorem D_congr {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (B : Type) [CommRing B]
    (i j : Algebra A B) (h : ∀ a, @algebraMap A B _ _ i a = @algebraMap A B _ _ j a) (x : MonoidAlgebra B G) :
    @GDet.D n A G _ _ D B _ i x = @GDet.D n A G _ _ D B _ j x := by
  have : i = j := Algebra.algebra_ext i j h
  subst this; rfl

private theorem ofT_gen {A G : Type} [CommRing A] [Group G] {m : ℕ} (y : Fin m → MonoidAlgebra A G) :
    ofT A G (MvPolynomial (Fin m) A) (Det.gen (A := A) y) = GDet.gen y := by

  simp only [Det.gen, GDet.gen, map_sum, ofT_tmul]
  rfl

private theorem ofT_map {A G : Type} [CommRing A] [Group G] (S : Type) [CommRing S] [Algebra A S]
    (x : S ⊗[A] MonoidAlgebra A G) :
    ofT A G S[X] (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A _) x) =
      MonoidAlgebra.mapRingHom G (C : S →+* S[X]) (ofT A G S x) := by
  induction x with
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul s y => ext1; ext1 g; simp [ofT_tmul]

private theorem chiS_eq {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) {m : ℕ}
    (x : MvPolynomial (Fin m) A ⊗[A] MonoidAlgebra A G) :
    D.toDet.chiS (MvPolynomial (Fin m) A) x =
      (D.map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)).chi (ofT A G _ x) := by
  have h : ofT A G (MvPolynomial (Fin m) A)[X] (X ⊗ₜ 1 -
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom A (MvPolynomial (Fin m) A) (MvPolynomial (Fin m) A)[X])
        (AlgHom.id A _) x) =
      MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C (ofT A G _ x) := by
    rw [map_sub, ofT_map, ofT_tmul, map_one, MonoidAlgebra.one_def, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  refine (congrArg (D.D (MvPolynomial (Fin m) A)[X]) h).trans ?_
  exact D_congr D (MvPolynomial (Fin m) A)[X] inferInstance
    ((algebraMap (MvPolynomial (Fin m) A) (MvPolynomial (Fin m) A)[X]).comp MvPolynomial.C).toAlgebra (fun a => rfl) _

private theorem coeff_lid {A G : Type} [CommRing A] [Group G] {m : ℕ} (β : Fin m →₀ ℕ)
    (w : MvPolynomial (Fin m) A ⊗[A] MonoidAlgebra A G) (g : G) :
    (TensorProduct.lid A (MonoidAlgebra A G) ((MvPolynomial.lcoeff A β).rTensor _ w)).coeff g =
      AddMonoidAlgebra.coeff ((ofT A G _ w).coeff g) β := by
  induction w with
  | add a b ha hb => simp only [map_add (f := _), MonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_add, ha, hb]
  | tmul s y => simp [ofT_tmul, mul_comm s, MvPolynomial.coeff_C_mul, mul_comm (y.coeff g)]

private theorem chElt_coeff {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) {m : ℕ}
    (y : Fin m → MonoidAlgebra A G) (β : Fin m →₀ ℕ) (g : G) :
    (D.toDet.chElt y β).coeff g = AddMonoidAlgebra.coeff ((Polynomial.aeval (GDet.gen y)
        ((D.map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)).chi (GDet.gen y))).coeff g)
      β := by
  rw [Det.chElt, coeff_lid, chiS_eq, ← Polynomial.aeval_algHom_apply, ofT_gen]

theorem UpperTheory.V.CA.d_toDet_CH :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G), D.toDet.CH = TwoSidedIdeal.span D.CH := by
  intro n A G _ _ D
  rw [Det.CH]
  congr 1
  ext1 z
  constructor
  · rintro ⟨m, y, β, rfl⟩
    exact ⟨m, y, β, chElt_coeff D y β⟩
  · rintro ⟨m, y, β, h⟩
    refine ⟨m, y, β, ?_⟩
    ext g
    rw [h, chElt_coeff]
