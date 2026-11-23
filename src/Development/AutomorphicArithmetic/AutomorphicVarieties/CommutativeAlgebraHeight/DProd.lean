module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DIdemRank
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
public import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom

@[expose] public section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section

variable {n : ℕ} {A ι : Type} [CommRing A] [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ i, Ring (E i)]
  [∀ i, Algebra A (E i)]

private theorem UpperTheory.V.CA.prod_piRight_apply (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] (∀ i, E i)) (i : ι) :
    Algebra.TensorProduct.piRight A S S E y i =
      Algebra.TensorProduct.map (AlgHom.id S S) (Pi.evalAlgHom A E i) y := by
  induction y with
  | tmul s y => simp
  | add a b ha hb => simp only [map_add (f := _), Pi.add_apply, ha, hb]

private theorem UpperTheory.V.CA.prod_piRight_map (S T : Type) [CommRing S] [Algebra A S] [CommRing T] [Algebra A T]
    (f : S →ₐ[A] T) (y : S ⊗[A] (∀ i, E i)) (i : ι) :
    Algebra.TensorProduct.piRight A T T E (Algebra.TensorProduct.map f (AlgHom.id A _) y) i =
      Algebra.TensorProduct.map f (AlgHom.id A _) (Algebra.TensorProduct.piRight A S S E y i) := by
  induction y with
  | tmul s y => simp
  | add a b ha hb => simp only [map_add (f := _), Pi.add_apply, ha, hb]

private theorem UpperTheory.V.CA.prod_single_smul (S : Type) [CommRing S] [Algebra A S] (b : S) (i : ι) :
    (Algebra.TensorProduct.piRight A S S E).symm (Pi.mulSingle i (b • (1 : S ⊗[A] E i))) =
      1 + (b - 1) ⊗ₜ[A] (Pi.single i 1 : ∀ i, E i) := by
  rw [AlgEquiv.symm_apply_eq]
  funext j
  rw [map_add (f := _), map_one, Pi.add_apply, Pi.one_apply, Algebra.TensorProduct.piRight_tmul]
  by_cases h : j = i
  · subst h
    simp only [Pi.mulSingle_eq_same, Pi.single_eq_same]
    rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      ← TensorProduct.add_tmul, add_sub_cancel]
  · simp [Pi.mulSingle_eq_of_ne h, Pi.single_eq_of_ne h]

private noncomputable def UpperTheory.V.CA.prodFactor (D : Det n A (∀ i, E i)) (i : ι) (r : ℕ)
    (hr : D.D A[X] (1 + X ⊗ₜ (Pi.single i 1 : ∀ i, E i)) = (1 + X) ^ r) : Det r A (E i) where
  D S _ _ := (D.D S).comp ((Algebra.TensorProduct.piRight A S S E).symm.toAlgHom.toMonoidHom.comp
    (MonoidHom.mulSingle (fun j => S ⊗[A] E j) i))
  nat S T _ _ _ _ f x := by
    change D.D T ((Algebra.TensorProduct.piRight A T T E).symm (Pi.mulSingle i _)) =
      f (D.D S ((Algebra.TensorProduct.piRight A S S E).symm (Pi.mulSingle i x)))
    rw [← D.nat]
    congr 1
    rw [AlgEquiv.symm_apply_eq]
    funext j
    rw [prod_piRight_map, AlgEquiv.apply_symm_apply]
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  homog S _ _ b x := by
    have h1 : b • x = (b • (1 : S ⊗[A] E i)) * x := by rw [smul_mul_assoc, one_mul]
    rw [h1, map_mul]
    congr 1
    change D.D S ((Algebra.TensorProduct.piRight A S S E).symm (Pi.mulSingle i _)) = _
    rw [prod_single_smul]
    have h2 := D.nat A[X] S (Polynomial.aeval (b - 1)) (1 + X ⊗ₜ (Pi.single i 1 : ∀ i, E i))
    rw [hr] at h2
    simpa using h2

end

theorem UpperTheory.V.CA.d_prod :
    ∀ {n : ℕ} {A ι : Type} [CommRing A] [IsLocalRing A] [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ i, Ring (E i)] [∀ i, Algebra A (E i)] (D : Det n A (∀ i, E i)), ∃ (m : ι → ℕ) (Ds : ∀ i, Det (m i) A (E i)), ∑ i, m i = n ∧ ∀ (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] (∀ i, E i)), D.D S y = ∏ i, ((Ds i).pull (Pi.evalAlgHom A E i)).D S y := by
  intro n A ι _ _ _ _ E _ _ D
  have hid : ∀ i, IsIdempotentElem (Pi.single i 1 : ∀ i, E i) := by
    intro i
    show _ * _ = _
    rw [← Pi.single_mul, one_mul]
  choose r hrle hr using fun i => d_idem_rank D (Pi.single i 1 : ∀ i, E i) (hid i)
  have hpull : ∀ (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] (∀ i, E i)) (i : ι),
      ((prodFactor E D i (r i) (hr i)).pull (Pi.evalAlgHom A E i)).D S y
        = D.D S ((Algebra.TensorProduct.piRight A S S E).symm
            (Pi.mulSingle i (Algebra.TensorProduct.piRight A S S E y i))) := by
    intro S _ _ y i
    rw [prod_piRight_apply]
    rfl
  have hprod : ∀ (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] (∀ i, E i)),
      D.D S y = ∏ i, ((prodFactor E D i (r i) (hr i)).pull (Pi.evalAlgHom A E i)).D S y := by
    intro S _ _ y
    simp only [hpull]
    let g : (∀ j, S ⊗[A] E j) →* S :=
      (D.D S).comp (Algebra.TensorProduct.piRight A S S E).symm.toAlgHom.toMonoidHom
    have hg : ∀ x, g x = D.D S ((Algebra.TensorProduct.piRight A S S E).symm x) := fun x => rfl
    calc D.D S y = g (Algebra.TensorProduct.piRight A S S E y) := by
          rw [hg, AlgEquiv.symm_apply_apply]
      _ = g (Finset.univ.noncommProd
            (fun i => Pi.mulSingle i (Algebra.TensorProduct.piRight A S S E y i))
            fun i _ j _ _ => Pi.mulSingle_apply_commute _ i j) := by
          rw [Finset.noncommProd_mulSingle]
      _ = ∏ i, g (Pi.mulSingle i (Algebra.TensorProduct.piRight A S S E y i)) :=
          (Finset.map_noncommProd _ _ _ g).trans (Finset.noncommProd_eq_prod _ _)
      _ = _ := by simp only [hg]
  refine ⟨r, fun i => prodFactor E D i (r i) (hr i), ?_, hprod⟩
  have h := hprod A[X] ((X : A[X]) • 1)
  simp only [Det.homog, map_one, mul_one] at h
  rw [Finset.prod_pow_eq_pow_sum] at h
  have h' := congrArg Polynomial.natDegree h
  simpa [Polynomial.natDegree_X_pow] using h'.symm
