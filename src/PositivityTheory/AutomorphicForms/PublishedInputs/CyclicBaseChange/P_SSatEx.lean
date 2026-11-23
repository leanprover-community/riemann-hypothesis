module

public import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.SConjSpaceC
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGLLocalComponentsEventuallySatake
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatLocFree
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep

namespace UpperTheory.CBC.SatakeParameterExistence

theorem re {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (n : ℕ) (π : UpperTheory.V.TR.CuspSub F n) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ B, π.HasSat v B :=
  UpperTheory.V.Af.Gk.satAE F n π

theorem cx (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {F : Type} [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (n : ℕ)
    (π : CuspSub F n) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ B, (CG.mk π).HasSat v B := by
  simpa only [CG.hasSat_mk] using UnrSat.eventually_hasSatGL_locRep hF F n π

theorem of_fin (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) : UpperTheory.CBC.SSatEx := by
  intro F _ _ n π
  match π with
  | @Cusp.cx _ _ _ _ hC π => exact cx hF n π
  | @Cusp.re _ _ _ _ hR π => exact re n π

end UpperTheory.CBC.SatakeParameterExistence
