module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

namespace UpperTheory.V.Br

section BC

variable {F E : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
  {a : ℕ}

structure IsBC0 (π : TR.CuspSub F a) (P : CuspSub E a) : Prop where
  inf : ∀ (τ : E →+* ℂ) (m : Multiset ℂ), π.HasInfChar (InfinitePlace.mk (τ.comp (algebraMap F E))) m → P.HasInfChar τ m
  unr : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ v : HeightOneSpectrum (𝓞 F),
    v.asIdeal = w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) → ∀ f : ℕ, normV w = normV v ^ f →
      ∃ B, π.HasSat v B ∧ (CG.mk P).HasSat w (B.map (· ^ f))

def SplitIso (π : TR.CuspSub F a) (P : CuspSub E a) : Prop :=
  ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (i : v.adicCompletion F ≃+* w.adicCompletion E),
    Continuous i → (∀ x : F, i (algebraMap F _ x) = algebraMap E _ (algebraMap F E x)) →
    ∀ σ σ', π.IsLocComp v σ → P.IsLocComp w σ' →
      ∃ e : σ.V ≃ₗ[ℂ] σ'.V, ∀ g x, e (σ.ρ g x) = σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom g) (e x)

structure IsBCw (π : TR.CuspSub F a) (P : CuspSub E a) : Prop extends IsBC0 π P where
  split : π.IsRegAlg → (∃ χ : HChar F, π.Polarized χ) → SplitIso π P

theorem IsBCw.of_isBC {π : TR.CuspSub F a} {P : CuspSub E a} (h : IsBC π P) : IsBCw π P := ⟨⟨h.inf, h.unr⟩, fun _ _ => h.split⟩

end BC

def QuadBCw : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E],
    Module.finrank F E = 2 → ∀ (a : ℕ) [Fact (a = 2)], 1 ≤ a → ∀ π : TR.CuspSub F a, π.IsRegAlg →
      (∃ η : HChar F, IsQuadCharOf E η ∧ IsoTwist π η) ∨ ∃ P : CuspSub E a, IsBCw π P

end UpperTheory.V.Br
