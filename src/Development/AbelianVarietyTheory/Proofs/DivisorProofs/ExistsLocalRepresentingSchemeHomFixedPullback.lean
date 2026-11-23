module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenBaseChangeStableSectionBasisStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedPullbackHomSchemeOfSectionBasesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixRepBasicOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeAndPullOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCommMonObjOfGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VeryAmpleAtBaseChange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.HomFixLocal

theorem exists_local_homFixRep : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → Out.RelAmple A L → Out.RelAmple B M → ∀ p : Sp Rg, ∃ U : (Sp Rg).Opens, p ∈ U ∧ ∃ (AU : Over (U).toScheme) (_ : GrpObj AU) (BU : Over (U).toScheme) (_ : GrpObj BU) (φA : AU.left ⟶ A.left) (φB : BU.left ⟶ B.left), IsGrpPullback AU A (U).ι φA ∧ IsGrpPullback BU B (U).ι φB ∧ ∃ R : HomFixRep AU BU (L.pull φA) (M.pull φB), QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  intro Rg _ _ A B _ _ _ _ L M hA hB hL hM rL rM aL aM p
  obtain ⟨k, hk, hva⟩ := GlobalTheory.RelAmpleFixed.veryAmpleAt_baseChange Rg B M hB hM aM
  obtain ⟨f₁, hp₁, hb₁⟩ := GlobalTheory.T.exists_basicOpen_baseChangeStable_sectionBasis Rg A L hA hL rL aL k hk p
  obtain ⟨f₂, hp₂, hb₂⟩ := GlobalTheory.T.exists_basicOpen_baseChangeStable_sectionBasis Rg B M hB hM rM aM k hk p
  have le₁ : PrimeSpectrum.basicOpen (f₁ * f₂) ≤ PrimeSpectrum.basicOpen f₁ := by
    rw [PrimeSpectrum.basicOpen_mul]; exact inf_le_left
  have le₂ : PrimeSpectrum.basicOpen (f₁ * f₂) ≤ PrimeSpectrum.basicOpen f₂ := by
    rw [PrimeSpectrum.basicOpen_mul]; exact inf_le_right
  have hp : p ∈ PrimeSpectrum.basicOpen (f₁ * f₂) := by
    rw [PrimeSpectrum.basicOpen_mul]; exact ⟨hp₁, hp₂⟩
  refine ⟨PrimeSpectrum.basicOpen (f₁ * f₂), hp, GlobalTheory.HomFixTransport.homFixRep_basicOpen Rg A B L M (f₁ * f₂) hL hM ?_ _ rfl⟩
  intro Af Bf _ _ φA φB hpA hpB
  haveI := GlobalTheory.isCommMonObj_of_grpPullback _ _ A Af _ φA hpA
  haveI := GlobalTheory.isCommMonObj_of_grpPullback _ _ B Bf _ φB hpB
  obtain ⟨hA', hL', rL', aL'⟩ := GlobalTheory.GrpPullbackPol.isAbelianScheme_and_pull_of_isGrpPullback _ _ _ A Af φA L hpA hA hL rL aL
  obtain ⟨hB', hM', rM', -⟩ := GlobalTheory.GrpPullbackPol.isAbelianScheme_and_pull_of_isGrpPullback _ _ _ B Bf φB M hpB hB hM rM aM
  exact GlobalTheory.T.exists_fixedPullbackHomScheme_of_sectionBases (Localization.Away (f₁ * f₂)) Af Bf (L.pull φA) (M.pull φB) k hA' hB' hL' hM' rL' rM' aL' hk
    (hva _ _ Bf φB hpB) (hb₁ _ le₁ Af φA hpA) (hb₂ _ le₂ Bf φB hpB)

end GlobalTheory.HomFixLocal
