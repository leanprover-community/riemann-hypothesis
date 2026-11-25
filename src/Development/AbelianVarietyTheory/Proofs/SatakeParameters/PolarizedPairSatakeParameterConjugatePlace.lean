module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGLLocalComponentsEventuallySatake
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.SatOfPol
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

namespace GlobalTheory.PolarizedSat

theorem hasSat_conjPlace : AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), GlobalTheory.ContraPair.PolarizedPair π χ → ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ B : Multiset ℂˣ, (CG.mk π).HasSat w B → (CG.mk π).HasSat (UpperTheory.V.Af.Bc.cPl w) (B.map fun α => α⁻¹ * (compNorm E χ).val w) := by
  intro hF E _ _ _ a π χ hpol
  have hu : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, (compNorm E χ).UnrAt w :=
    Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified _)
  have hs : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, (CG.mk π).HasSat (UpperTheory.V.Af.Bc.cPl w) B :=
    (conjSrc_injective _).tendsto_cofinite.eventually (GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep hF E a π)
  filter_upwards [hu, hs] with w hw hB'e B hB
  obtain ⟨B', hB'⟩ := hB'e
  have e := UpperTheory.V.Br.satOfPol E a π _ hpol.dual w hw B B' hB hB'
  have e2 : B' = B.map fun α => α⁻¹ * (compNorm E χ).val w := by
    have e3 := congrArg (Multiset.map fun z : ℂˣ => z⁻¹) e
    rw [Multiset.map_map, Multiset.map_map] at e3
    simp only [Function.comp_def, inv_inv, Multiset.map_id'] at e3
    rw [e3]
    exact Multiset.map_congr rfl fun α _ => by rw [mul_inv_rev, inv_inv, mul_comm]
  rw [← e2]
  exact hB'

end GlobalTheory.PolarizedSat
