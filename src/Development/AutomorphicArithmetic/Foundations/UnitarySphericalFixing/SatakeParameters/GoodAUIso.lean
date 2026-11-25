module

public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SwOn
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAutomorphicSideEmptyLocal
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

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain
open UpperTheory.Zero.LLC

namespace UpperTheory.One.M

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def GoodAU (π : NG.AutRep L n) : Prop := ∀ (s : SplitPlace L) σ, IsLocS π.S s σ → Good (GlobalTheory.LocLanglands.cls σ)

def NoSplit (L : Type) [Field L] [NumberField L] [IsCMField L] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : Prop :=
  ∀ s : SplitPlace L, s.v ≠ v

def SphAtG (π : NG.AutRep L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : Prop :=
  π.SphAt v ∧ (NoSplit L v → GoodAU π)

theorem goodAU_iso {π π' : NG.AutRep L n} (h : π.Iso π') (hg : GoodAU π) : GoodAU π' := fun s σ' hσ' => by
  obtain ⟨x, σ₀, σ, e, hσ, hx⟩ := GlobalTheory.AutQuot.locAt_of_split π s
  have h1 : x = GlobalTheory.LocLanglands.cls σ' := GlobalTheory.AutQuot.locAt_unique h ⟨σ₀, σ, e, hσ, hx⟩ ⟨s, σ', rfl, hσ', HEq.rfl⟩
  have key : ∀ (w : HeightOneSpectrum (𝓞 L)) (e : σ₀.w = w) (y : GlobalTheory.LocGL.IrrGL (k := w.adicCompletion L)),
      HEq (GlobalTheory.LocLanglands.cls σ) y → Good y := by
    rintro _ rfl y hy
    exact eq_of_heq hy ▸ hg σ₀ σ hσ
  exact h1 ▸ key _ e x hx

namespace Old

end Old

namespace New

def Sph0 (π : NG.AutRep L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : Prop := π.SphAt v

theorem sphGood {π : NG.AutRep L n} {v} (h : SphAtG π v) : NoSplit L v → GoodAU π := h.2

theorem sphMk {π : NG.AutRep L n} {v} (h : Sph0 π v) (hg : NoSplit L v → GoodAU π) : SphAtG π v := ⟨h, hg⟩

theorem sphAt_iso {π π' : NG.AutRep L n} (h : π.Iso π') {v} (hs : SphAtG π v) : SphAtG π' v :=
  ⟨GlobalTheory.AutQuot.sphAt_iso h hs.1, fun hv => goodAU_iso h (hs.2 hv)⟩

end New

end UpperTheory.One.M

end
