module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineWeilDeligneSpaceRestrictionEquiv
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

theorem _root_.GlobalTheory.T.fontaineWeilDeligneSpace_restriction_equiv : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (ι : Qbar l ≃+* ℂ) (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (O O' : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O'] (Bw : LocBridge l K Ω (Dec (F := K) A) O) (Bw' : LocBridge l L Ω (Dec (F := L) A) O') (hj : GlobalTheory.Pst.Induces Bw) (hj' : GlobalTheory.Pst.Induces Bw') (hle : Bw.Kw.1 ≤ Bw'.Kw.1), (∀ (σ : Weil h) (σ' : Weil h'), (∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) → (weilToGK Bw' h' σ' : GQ l) = (weilToGK Bw h σ : GQ l)) → ∀ (LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (GlobalTheory.Pst.resTo ρ hle))], IsPst P ρ → ∃ e : WDSpace P ι ρ ≃ₗ[ℂ] WDSpace P ι (GlobalTheory.Pst.resTo ρ hle), (∀ (σ : Weil h) (σ' : Weil h'), (∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) → ∀ x, e (wdRho P ι Bw h hj ρ σ x) = wdRho P ι Bw' h' hj' (GlobalTheory.Pst.resTo ρ hle) σ' (e x)) ∧ ∀ x, e (wdN P ι ρ x) = wdN P ι (GlobalTheory.Pst.resTo ρ hle) (e x) := by
  first | exact @GlobalTheory.Pst.ResLetter.wdSpace_resTo_equiv | exact GlobalTheory.Pst.ResLetter.wdSpace_resTo_equiv | (intros; apply GlobalTheory.Pst.ResLetter.wdSpace_resTo_equiv <;> assumption)
