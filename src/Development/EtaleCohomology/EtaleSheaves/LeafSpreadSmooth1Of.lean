module

public import Development.EtaleCohomology.EtaleSheaves.SpreadingOutQuasiFiniteness
public import Development.EtaleCohomology.EtaleSheaves.LeafSpreadSmoothAffSmPf
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
public import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut TensorProduct

namespace LateralTheory.E.SpreadingOutSmoothness

theorem stepB {R K B A : Type} [CommRing R] [CommRing K] [CommRing B] [CommRing A] [Algebra R K] [Algebra R A]
    [Algebra R B] [Algebra K B] [IsScalarTower R K B] [Algebra A B] [IsScalarTower R A B] (M : Submonoid R)
    [IsLocalization M K] [IsLocalization (Algebra.algebraMapSubmonoid A M) B] [Algebra.Smooth K B]
    (Q : Ideal B) [Q.IsPrime] : Algebra.IsSmoothAt R (Q.comap (algebraMap A B)) := by
  haveI : Algebra.FormallySmooth R K := Algebra.FormallySmooth.of_isLocalization M
  haveI : Algebra.FormallySmooth K (Localization.AtPrime Q) := inferInstance
  haveI : Algebra.FormallySmooth R (Localization.AtPrime Q) := Algebra.FormallySmooth.comp R K _
  haveI := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (Algebra.algebraMapSubmonoid A M) (Localization.AtPrime Q) Q
  exact Algebra.FormallySmooth.of_equiv ((IsLocalization.algEquiv (Q.comap (algebraMap A B)).primeCompl
    (Localization.AtPrime Q) _).restrictScalars R)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem algDescend (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω)
    (A : Type) [CommRing A] [Algebra R A] (hfp : Algebra.FinitePresentation R A) (hs : Algebra.Smooth Ω (Ω ⊗[R] A))
    (P : PrimeSpectrum (Ω ⊗[R] A)) :
    PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] Ω ⊗[R] A).toRingHom P ∈ Algebra.smoothLocus R A := by
  letI : Algebra (FractionRing R) Ω := FractionRing.liftAlgebra R Ω
  haveI : IsScalarTower R (FractionRing R) Ω := FractionRing.isScalarTower_liftAlgebra R Ω
  let e := Algebra.TensorProduct.cancelBaseChange R (FractionRing R) Ω Ω A
  haveI : Algebra.Smooth Ω (Ω ⊗[FractionRing R] (FractionRing R ⊗[R] A)) := Algebra.Smooth.of_equiv e.symm
  haveI : Module.Free (FractionRing R) Ω := Module.Free.of_divisionRing _ Ω
  haveI : Algebra.Smooth (FractionRing R) (FractionRing R ⊗[R] A) :=
    Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat Ω
  letI : Algebra A (FractionRing R ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  haveI : IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) (FractionRing R ⊗[R] A) :=
    IsLocalization.tensorRight _ _
  let φ : FractionRing R ⊗[R] A →+* Ω ⊗[R] A := e.toRingHom.comp
    (Algebra.TensorProduct.includeRight : FractionRing R ⊗[R] A →ₐ[FractionRing R] Ω ⊗[FractionRing R] _).toRingHom
  haveI : (P.asIdeal.comap φ).IsPrime := Ideal.comap_isPrime _ _
  have hφ : φ.comp (algebraMap A (FractionRing R ⊗[R] A)) =
      (Algebra.TensorProduct.includeRight : A →ₐ[R] Ω ⊗[R] A).toRingHom := by
    ext a
    show e (1 ⊗ₜ (1 ⊗ₜ a)) = 1 ⊗ₜ a
    rw [Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]
  have hc : PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] Ω ⊗[R] A).toRingHom P =
      ⟨(P.asIdeal.comap φ).comap (algebraMap A (FractionRing R ⊗[R] A)), inferInstance⟩ := by
    ext1; simp only [PrimeSpectrum.comap_asIdeal, Ideal.comap_comap, hφ]
  rw [hc]
  exact stepB (K := FractionRing R) (nonZeroDivisors R) (P.asIdeal.comap φ)

def LeafAlgDescend : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω)
    (A : Type) [CommRing A] [Algebra R A], Algebra.FinitePresentation R A → Algebra.Smooth Ω (Ω ⊗[R] A) →
    ∀ P : PrimeSpectrum (Ω ⊗[R] A),
      PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] Ω ⊗[R] A).toRingHom P ∈ Algebra.smoothLocus R A

def LeafStalkOfAlg : Prop := LeafAlgDescend → LateralTheory.E.LeafSpreadSmoothAffSmPf.LeafStalkDescend

theorem leafAlgDescend : LeafAlgDescend := fun k _ Ω _ _ R A _ _ hfp hs P => algDescend k Ω R A hfp hs P

theorem LeafSpreadSmooth1_of (hB : LateralTheory.E.LeafSpreadSmoothPf.LeafSpreadRelDim) (hT : LeafStalkOfAlg) :
    LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadSmooth1 :=
  LateralTheory.E.LeafSpreadSmoothPf.LeafSpreadSmooth_of
    (LateralTheory.E.LeafSpreadSmoothAffSmPf.LeafSpreadSmoothAffSm_of (hT leafAlgDescend)) hB

end LateralTheory.E.SpreadingOutSmoothness

end
