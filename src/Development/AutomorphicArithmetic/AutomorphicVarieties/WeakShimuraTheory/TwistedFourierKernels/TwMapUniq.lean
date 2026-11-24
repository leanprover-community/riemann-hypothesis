module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.IsTwistTwD
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGext
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ExistsDeterminantPairMapOfAlgHom
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

open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5

theorem UpperTheory.V.Ws.H5.twMapUniq :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} (B : UniversalOrdinaryDeterminantRing r) {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (f₀ : B.B →+* R) (γ : F.G₀ →* Rˣ) (f f' : B.B →ₐ[O] R), TwMap B f₀ (f : B.B →+* R) γ → TwMap B f₀ (f' : B.B →+* R) γ → f = f' := by
  intro l _ F O _ _ _ n r B R _ _ _ f₀ γ f f' hf hf'
  obtain ⟨p, hp⟩ := exists_determinantPair_map_of_algHom l F O n r B.B R f B.u
  have hs : ∀ (φ : B.B →+* R) (g : F.G₀), MonoidAlgebra.mapRingHom F.G₀ φ (MonoidAlgebra.single g 1) = MonoidAlgebra.single g 1 := by
    intro φ g
    simp [MonoidAlgebra.mapRingHom]
  have hD : B.u.D.map (f' : B.B →+* R) = B.u.D.map (f : B.B →+* R) := by
    apply CA.d_gext
    intro g i _ hi
    have e1 := ((CA.d_gmap B.u.D).2.2.1 (f : B.B →+* R) (MonoidAlgebra.single g 1)).2 i
    have e2 := ((CA.d_gmap B.u.D).2.2.1 (f' : B.B →+* R) (MonoidAlgebra.single g 1)).2 i
    rw [hs] at e1 e2
    rw [e1, e2, hf.1 g i hi, hf'.1 g i hi]
  have hψ : ∀ v i, pushCh (f' : B.B →+* R) (B.u.ψ v i) = pushCh (f : B.B →+* R) (B.u.ψ v i) := by
    intro v i
    ext g
    simp only [pushCh, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, MonoidHom.coe_coe]
    exact (hf'.2 v i g).trans (hf.2 v i g).symm
  have hp' : B.u.Maps (f' : B.B →+* R) p.D p.ψ := by
    unfold Pair.Maps at hp ⊢
    exact ⟨hD.trans hp.1, fun v i => (hψ v i).trans (hp.2 v i)⟩
  obtain ⟨h, _, huniq⟩ := B.univ R p
  exact (huniq f hp).trans (huniq f' hp').symm
