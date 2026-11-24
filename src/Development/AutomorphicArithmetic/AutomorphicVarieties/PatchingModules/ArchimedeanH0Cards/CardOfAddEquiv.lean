module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.PushforwardPreservesSelmerCocycles
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.TaylorWilesObstructionBound
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.H2RightExactModLOfH3Subsingleton
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ScalQuot
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
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

private theorem UpperTheory.V.Pa.B2.card_of_addEquiv {X Y : Type} {_ : Add X} {_ : Add Y} (e : X ≃+ Y) :
    Nat.card X = Nat.card Y ∧ (Finite Y → Finite X) :=
  ⟨Nat.card_congr e.toEquiv, fun _ => Finite.of_injective e e.injective⟩

theorem UpperTheory.V.Pa.B2.arLoc :
    CohP → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (B : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver B v → FinH l (Dec (F := F) B) ∧ SecondCohomologyRightExactModL l (Dec (F := F) B) ∧ ((((l : ℕ) : 𝓞 F) ∈ v.asIdeal → LocE l (Dec (F := F) B) (locDeg v)) ∧ (((l : ℕ) : 𝓞 F) ∉ v.asIdeal → LocE l (Dec (F := F) B) 0)) := by
  intro hP F Ω _ _ _ _ _ l _ B v hB
  have key : ∀ (A : Type) [CommRing A] (M : FRep A (Dec (F := F) B)), (∀ m : M.X, l • m = 0) →
      (Finite (H1 M.ρ) ∧ Finite (H2 M.ρ)) ∧
      ((((l : ℕ) : 𝓞 F) ∈ v.asIdeal →
        Nat.card (H1 M.ρ) = Nat.card (H0 M.ρ) * Nat.card (H2 M.ρ) * Nat.card M.X ^ locDeg v) ∧
       (((l : ℕ) : 𝓞 F) ∉ v.asIdeal →
        Nat.card (H1 M.ρ) = Nat.card (H0 M.ρ) * Nat.card (H2 M.ρ) * Nat.card M.X ^ 0)) := by
    intro A _ M hl
    letI : Module (ZMod (l ^ 1)) M.X := AddCommGroup.zmodModule (fun m => by rw [pow_one]; exact hl m)
    obtain ⟨hc, ⟨e0⟩, ⟨e1, -⟩, ⟨e2, -⟩⟩ := scal A _ M (l ^ 1)
    have hf := hP.lf F Ω l 1 M.X B (GlobalTheory.Published.zmodRep (l ^ 1) M.ρ) v one_pos hB hc
    have he := hP.le F Ω l 1 M.X B (GlobalTheory.Published.zmodRep (l ^ 1) M.ρ) v one_pos hB hc
    have c0 : Nat.card (H0 M.ρ) = Nat.card (H0 (GlobalTheory.Published.zmodRep (l ^ 1) M.ρ)) :=
      (card_of_addEquiv e0).1
    have c1 : Nat.card (H1 M.ρ) = Nat.card (H1 (GlobalTheory.Published.zmodRep (l ^ 1) M.ρ)) :=
      (card_of_addEquiv e1).1
    have c2 : Nat.card (H2 M.ρ) = Nat.card (H2 (GlobalTheory.Published.zmodRep (l ^ 1) M.ρ)) :=
      (card_of_addEquiv e2).1
    rw [c0, c1, c2, pow_zero, mul_one]
    have f1 : Finite (H1 M.ρ) := (card_of_addEquiv e1).2 hf.2.1
    have f2 : Finite (H2 M.ρ) := (card_of_addEquiv e2).2 hf.2.2.1
    exact ⟨⟨f1, f2⟩, he⟩
  refine ⟨fun A _ M hl => (key A M hl).1, H2_right_exact_mod_l_of_H3_subsingleton l _ fun A _ M hl => ?_,
    fun h A _ M hl => (key A M hl).2.1 h, fun h A _ M hl => (key A M hl).2.2 h⟩
  exact (GlobalTheory.Published.cohDimTwoLocal_of_localFiniteness hP.lf).of_nsmul l 1
    (fun m => by rw [pow_one]; exact hl m) M.ρ hB M.cont 3 le_rfl
