module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.SplitIrr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.AutP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AdmissibleLevelRestriction.UnlOfOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.FlagLaws
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.TeichNotLt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.UnlPlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.Z.Win.A4

section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {n : ℕ}

def SafeRA (l : ℕ) [Fact l.Prime] (M : ℕ) (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  (l ∣ M ∧ UnlAll r) ∨ ∀ i j, m i ≠ m j + 1

def SafePA (l : ℕ) [Fact l.Prime] (M : ℕ) (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  (l ∣ M ∧ PotAll r) ∨ ∀ i j, m i ≠ m j + 1

variable [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {M : ℕ} {m : Fin n → ℤ} {r : G F Ω →* GL (Fin n) (Qbar l)}

theorem safeUGap' (_ : Level l M m r) (h : ∀ i j, m i ≠ m j + 1) : SafeRA l M m r := Or.inr h

theorem safeRes' (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] (h : SafePA l M m r) :
    SafePA l M m (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) :=
  h.imp_left fun ⟨h1, h2⟩ => ⟨h1, fun w hw => (((flagLaws F Ω l n r).2.2.2 K).2.2 w hw).1 (h2 _ (by
    change algebraMap (𝓞 F) (𝓞 K) (l : 𝓞 F) ∈ w.asIdeal
    rwa [map_natCast]))⟩

theorem unlAll_of (h : Th.Unl l M m r) : UnlAll r := fun v hv => by
  obtain ⟨A, hA, κ, ⟨-, -, hf, -⟩, hu⟩ := h v hv
  exact unlOfOne F Ω l n r v A hA κ hf hu
end

theorem safe4' {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (hD : D.Good)
    (N : ℕ) (hN : 1 ≤ N) (h1 : Af.KillsMu N D.ψ) (h2 : Af.KillsMu N D.ξ) (h3 : Af.KillsMu N D.om) (r : G ℚ Ω →* M4 (PadicAlgCl l))
    (hr : D.EPt r) : SafeRA l N ![(D.e : ℤ) + 1, D.e, 1, 0] r.toHomUnits :=
  Or.inl ⟨Lev.teichDvd D hD N hN h3, unlAll_of (Th.spUnl D hD N hN h1 h2 h3 r hr)⟩

end UpperTheory.V.Z.Win.A4
