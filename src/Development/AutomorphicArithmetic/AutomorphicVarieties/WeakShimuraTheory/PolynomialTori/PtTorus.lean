module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ExDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.ClosedOfSet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.OnCompTorus
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Po.ptTorus :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (r r' : Lift c.O D.rbar R) (s : Rˣ × Rˣ),
      res c.O R s.1 = 1 → res c.O R s.2 = 1 → (∀ g, r'.hom g = tconj s (r.hom g)) → D.IsPt r → D.IsPt r' := by
  intro Ω _ _ _ l _ c D _ R _ _ _ r r' s h1 h2 hc hP
  have hone : ∀ X : UpperTheory.V.GradeZeroInterpolatingElement.M4 R, X = 1 → UpperTheory.V.GradeZeroInterpolatingElement.tconj s X = 1 := by
    rintro X rfl
    ext i j
    fin_cases i <;> fin_cases j <;> simp [UpperTheory.V.GradeZeroInterpolatingElement.tconj, UpperTheory.V.GradeZeroInterpolatingElement.wv, UpperTheory.V.GradeZeroInterpolatingElement.wt, Matrix.one_apply]
  have hent : ∀ (X : UpperTheory.V.GradeZeroInterpolatingElement.M4 R) (i j : Fin 4), UpperTheory.V.GradeZeroInterpolatingElement.tconj s X i j = 0 ↔ X i j = 0 := by
    intro X i j
    simp only [UpperTheory.V.GradeZeroInterpolatingElement.tconj, Matrix.of_apply]
    constructor
    · intro h
      have := congrArg (fun x => (↑(UpperTheory.V.GradeZeroInterpolatingElement.wv s (UpperTheory.V.GradeZeroInterpolatingElement.wt i j))⁻¹ : R) * x) h
      simpa [← mul_assoc] using this
    · intro h
      simp [h]
  have hEl' : D.hEl r'.hom = UpperTheory.V.GradeZeroInterpolatingElement.tconj s (D.hEl r.hom) := by
    simp only [UpperTheory.V.GradeZeroInterpolatingElement.Raw.hEl, hc]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, UpperTheory.V.GradeZeroInterpolatingElement.tconj, Matrix.of_apply]
    rw [mul_add, mul_smul_comm]
  obtain ⟨hb, h02, h20⟩ := hP.nrm
  refine ⟨?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g
    rw [hc]
    exact UpperTheory.V.Ws.Po.gsp_conj s (hP.mult g)
  · intro A hA g hg hb'
    rw [hc]
    exact hone _ (hP.unr A hA g hg hb')
  · intro i j hij
    rw [hc, hent]
    exact hb i j hij
  · rw [hEl', hent]
    exact h02
  · rw [hEl', hent]
    exact h20
  · exact UpperTheory.V.Ws.Po.onCompTorus c.O _ (D.rbarAt l) D.condL (D.r0At l)
      (fun R _ _ _ R' _ _ _ f ρ h => UpperTheory.V.GradeZeroInterpolatingElement.Ex.condL_map D f ρ h)
      (fun R _ _ _ ρ ρ' t h hq => UpperTheory.V.Ws.Po.torusL D ρ ρ' t h hq)
      R (D.loc r l) (D.loc r' l) s h1 h2 (fun g => hc g) hP.atL
  · intro p hp
    exact UpperTheory.V.Ws.Po.onCompTorus c.O _ (D.rbarAt p) (D.condP p) (D.r0At p)
      (fun R _ _ _ R' _ _ _ f ρ h => UpperTheory.V.GradeZeroInterpolatingElement.Ex.condP_map D p f ρ h)
      (fun R _ _ _ ρ ρ' t h hq => UpperTheory.V.Ws.Po.torusP D p ρ ρ' t h hq)
      R (D.loc r p) (D.loc r' p) s h1 h2 (fun g => hc g) (hP.atP p hp)
