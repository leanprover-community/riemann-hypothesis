module

public import Mathlib.Data.Rat.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharInertiaSurjective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ClassIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.IneFixRoots
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.UnitsMapSurjOfZmod
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFiniteAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published

namespace UpperTheory.V.Sd.EG

section Norm

variable {l : ℕ} [hl : Fact l.Prime]

end Norm

private theorem primRam_lift (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (r : ℕ) (hr : r.Prime)
    (A : ValuationSubring Ω) (hA : A.valuation (r : Ω) < 1) (u : (ZMod N)ˣ)
    (hu : u ∈ (ZMod.unitsMap (Nat.ordCompl_dvd N r)).ker) :
    ∃ σ ∈ Ine (F := ℚ) A, Chr.cls ℚ Ω N σ = u := by
  have : Fact r.Prime := ⟨hr⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero (ordCompl[r] N) := ⟨(Nat.ordCompl_pos r (NeZero.ne N)).ne'⟩
  have hcop : (ordCompl[r] N).Coprime r := (Nat.coprime_ordCompl hr (NeZero.ne N)).symm
  have hone : ∀ ζ : Ω, ζ ^ ordCompl[r] N = 1 →
      ζ ^ ((1 : (ZMod (ordCompl[r] N))ˣ) : ZMod (ordCompl[r] N)).val = ζ := fun ζ hζ => by
    rw [Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ, pow_one]
  obtain ⟨w, hw⟩ := KStar.TotallyRealRoots.redPow_surjective (l := r) (N.factorization r) (ZMod.unitsMap (Nat.ordProj_dvd N r) u)
  obtain ⟨σ, hσ, hσw⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω r A hA w
  refine ⟨σ, hσ, (Chr.clsFacts ℚ Ω N).2.2.1 σ u ?_⟩
  refine (LDataCardLeFinrank.classIff Ω r N σ.toRingEquiv u).2 ⟨fun ζ hζ => ?_, ?_⟩
  · rw [MonoidHom.mem_ker.1 hu, hone ζ hζ]
    exact (LDataCardLeFinrank.ineFixRoots ℚ Ω r A hA _ hcop ζ hζ).2 σ hσ
  · have hc : cyclotomicCharacter Ω r σ.toRingEquiv = w := hσw
    rw [hc, hw]

section Gal

variable {l : ℕ} [hl : Fact l.Prime] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

private theorem ram {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (f : ℂ →+* Qbar l) {p : ℕ} (hp : p.Prime)
    (hpN : p ∣ N) {A : ValuationSubring Ω} (hA : A.valuation (p : Ω) < 1) :
    ¬ Ine (F := ℚ) A ≤ (Chr.dirG ℚ Ω (χ.ringHomComp f)).ker := fun hall => by
  have hft : χ.FactorsThrough (ordCompl[p] N) := by
    refine (DirichletCharacter.factorsThrough_iff_ker_unitsMap (Nat.ordCompl_dvd N p)).2 fun u hu => ?_
    obtain ⟨σ, hσ, rfl⟩ := primRam_lift Ω N p hp A hA u hu
    have h1 := congrArg Units.val (MonoidHom.mem_ker.1 (hall hσ))
    refine MonoidHom.mem_ker.2 (Units.ext (f.injective ?_))
    rw [Units.val_one, map_one]
    exact h1
  have hd : χ.conductor ≤ ordCompl[p] N := Nat.sInf_le hft
  rw [hχ] at hd
  have := Nat.div_lt_self (NeZero.pos N) (Nat.one_lt_pow (hp.factorization_pos_of_dvd (NeZero.ne N) hpN).ne' hp.one_lt)
  omega

end Gal

end UpperTheory.V.Sd.EG
