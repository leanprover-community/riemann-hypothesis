module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CrisToODToOCr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeExponentsAinfComparisonStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KisinModuleTensorBdRPlusEqLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerSubOneAinfPropertiesCompatibleRootsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per



private theorem UpperTheory.KN.tame_identification_unit (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) :
    ∃ u : OA l O, IsUnit (toOD l O u) ∧ ∀ i : ι, ∃ z : TW (OA l O) T,
      I.j (inclV l O ι (Pi.single i u)) = TWincl (inclO l O) T z := by
  obtain ⟨⟨ε, hε⟩, hεall⟩ := GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l
  set δ : OCb l := (frobeniusEquiv (OCb l) l).symm ε with hδdef
  have hδ : δ ^ l = ε := frobeniusEquiv_symm_pow_p (OCb l) l ε
  obtain ⟨-, -, hθ, -⟩ := hεall ε δ hε hδ
  obtain ⟨α, β, hα, hβ⟩ := P.exists_exponents
  obtain ⟨hK1, hK2, -, -⟩ := GlobalTheory.T.breuilKisin_lattice_exponents_ainf_comparison l a e O K t ϖ ι P T I α β hα hβ ε δ hε hδ
  set ν : OA l O := (1 : O) ⊗ₜ[ℤ_[l]] muOf δ with hν
  have hpow : ∀ k : ℕ, (1 : O) ⊗ₜ[ℤ_[l]] (muOf δ ^ k) = ν ^ k := fun k => by
    rw [hν, Algebra.TensorProduct.tmul_pow, one_pow]
  simp only [hpow] at hK1 hK2
  have hu : IsUnit (toOD l O ν) := by
    have h1 : IsUnit (ainfToBdRp l (muOf δ)) := (GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ (by
      change Per.θD l (GlobalTheory.MemLoc.aDp l (muOf δ)) ≠ 0
      rw [(GlobalTheory.MemLoc.thetaD_props l).2.2.2.1]
      intro h
      exact hθ (Subtype.ext h))
    have h2 : toOD l O ν = (Algebra.TensorProduct.includeRight : Per.BdRp l →ₐ[ℤ_[l]] OD l O)
        (ainfToBdRp l (muOf δ)) := by
      simp [hν, toOD]
    rw [h2]
    exact h1.map _
  choose z hz using fun i => hK2 (inclV l O ι (Pi.single i 1)) ⟨_, rfl⟩
  refine ⟨ν ^ α, ?_, fun i => ⟨z i, ?_⟩⟩
  · rw [map_pow]
    exact hu.pow α
  · have hc : inclV l O ι (Pi.single i (ν ^ α)) = inclO l O (ν ^ α) • inclV l O ι (Pi.single i 1) := by
      rw [← GlobalTheory.DeRhamIdent.inclV_smul]
      congr 1
      funext j
      simp [Pi.single_apply]
    rw [hc, hz i]

theorem _root_.UpperTheory.KN.exists_unit_identification_single_integral :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), ∃ u : OA l ↥(OL LL), IsUnit (toOD l ↥(OL LL) u) ∧ ∀ i : ι, ∃ z : TW (OA l ↥(OL LL)) T, I.j (inclV l ↥(OL LL) ι (Pi.single i u)) = TWincl (inclO l ↥(OL LL)) T z := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ P T I
  exact UpperTheory.KN.tame_identification_unit l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P T I
