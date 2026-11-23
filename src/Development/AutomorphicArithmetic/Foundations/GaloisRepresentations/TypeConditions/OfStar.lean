module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.WeightsConjBis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.InePolOfUnr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.PowEqOneOfRoots
public import Development.AutomorphicArithmetic.NaturalDivisibility.ExistsContinuousRingEquivPadicOfTotallySplit
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open UpperTheory.GalStar
open scoped commutatorElement

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalS

section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem star_guard {y : WD h} (k : NcW y) : (IsQpBig w y.lpDim ∧ TmW y ∧ UpperTheory.GalStar.Sqf y) ∨ Tor y := by
  by_cases hs : ∃ p : ℕ, p.Prime ∧ w ∈ placesOver E p ∧ (placesOver E p).ncard = Module.finrank ℚ E ∧
      (y.lpDim = 1 ∨ 16 * y.lpDim ^ 2 < p)
  · have ht : thr w y.lpDim = 2 := if_pos hs
    obtain ⟨p, hp, hw, hc, hb⟩ := hs
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨i, hi⟩ := UpperTheory.exists_continuous_ringEquiv_padic_of_totally_split E w p hw hc
    exact Or.inl ⟨⟨p, inferInstance, i, hi, hb⟩, k.1, fun γ hγ hg z hz => k.2.2 γ hγ hg z (by rwa [ht])⟩
  · exact Or.inr (tor_of_ncW (if_neg hs) k)

theorem tor_of_unr {y : WD h} (u : y.unr) : Tor y := fun s t => by
  have hd : deg ⁅s, t⁆ = 0 := by simp [commutatorElement_def]
  have := inePol_of_unr u (deg_eq_zero_iff.1 hd)
  rwa [WD.inePol_of_mem _ (⁅s, t⁆ : ↥(Weil h)).2] at this

theorem away_nice {x y : WD h} (a : AwayB x y) (k : NcW y) :
    x.mono0 ∧ ∀ g : ↥(Weil h), deg g = 0 → x.charPol g = y.charPol g := by
  rcases star_guard k with ⟨q, t, s⟩ | t
  · exact a.tame0 q t s k.2.1
  · rw [a.tor t k.2.1]; exact ⟨k.2.1, fun _ _ => rfl⟩

theorem aw_of_away {x y : WD h} (a : AwayB x y) : Aw x y :=
  ⟨a.dim, fun u => a.tor (tor_of_unr u) (WD.unr_mono0 _ u), fun k => (away_nice a k).2, fun k => (away_nice a k).1⟩
end

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  [IsAlgClosure E Ω] [IsCMField E]


end UpperTheory.GalS
