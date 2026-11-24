module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.UnitaryTwoForm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.Strong
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeEigenvalueBasicProperties
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.NormAbsPowUnif
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PlainIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.SphUnl
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.Bridge

@[expose] public section

theorem UpperTheory.V.Z.Sym.W.glueW :
    UpperTheory.V.Z.Sym.W.GlueW := by
  intro L Ω _ _ _ _ _ _ l _ ι R h π _ hπ
  obtain ⟨t, ht⟩ := UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.winOfP_of UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.plainIff UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.winOf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.sphUnl
    L 3 (by norm_num) π
  refine ⟨t, fun w => ?_⟩
  obtain ⟨π', hπ', hc⟩ := h w
  have e : π' = π := by
    refine GlobalTheory.CuspRep.CuspSub.ext (UpperTheory.V.Af.strongMultOneC L 3 π' π ?_)
    filter_upwards [hπ'.2, hπ.2] with v h1 h2
    obtain ⟨B, hB, hE⟩ := h1
    obtain ⟨B', hB', hE'⟩ := h2
    have e : B = B' := (UpperTheory.hecke_eigenvalue_basic_properties L Ω l ι v).2.2 3 R B B' hE hE'
    exact ⟨B, (GlobalTheory.CuspRep.CG.hasSat_mk π' v B).1 hB, (GlobalTheory.CuspRep.CG.hasSat_mk π v B).1 (e ▸ hB')⟩
  subst e
  rcases hc with ⟨B, hB⟩ | hp
  · exact (ht w).2 B hB
  · exact (ht w).1 hp
