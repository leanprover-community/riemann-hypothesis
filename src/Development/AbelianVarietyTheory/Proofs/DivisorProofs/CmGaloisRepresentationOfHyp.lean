module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologicalLocalComponentExponents
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Data.Multiset.Functor
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasString
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableTrivChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmGaloisRepresentationCrystallineStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatGLOfIsCompAlongSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSphericalOfIsCompAlongSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeLinearFactorsRegroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpehInfMapSubEqSumTwists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpehPartIsRun
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeSpehOfDiscreteSeries
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologicalLocalComponentExponentsStatement, Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryStringForcesLongPart, Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmGaloisRepresentationOfHyp

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologicalLocalComponentExponentsStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologicalLocalComponentExponentsStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologicalLocalComponentExponents\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.cohomological_local_component_exponents : GlobalTheory.Published.ClozelCohomological → GlobalTheory.Published.CohomologicalCsdTempered →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a → ∀ P : CuspSub E a, P.IsCsd →
  ∀ m : (E →+* ℂ) → Multiset ℂ, (∀ τ, P.HasInfChar τ (m τ)) → (∀ τ, (m τ).Nodup) →
  ∀ f : ℂ, (∀ τ, ∀ z ∈ m τ, ∃ k : ℤ, z = f + k) →
  ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), P.IsLocComp w σ →
    ∀ S : Multiset ℂˣ, GlobalTheory.LFun.HasSatGL w σ.ρ S → ∀ s ∈ S, ‖(s : ℂ)‖ = 1 := by
  first | exact @GlobalTheory.TempSat.norm_satake_eq_one
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologicalLocalComponentExponentsStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryStringForcesLongPart =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryStringForcesLongPart", "h": "module\n\npublic import Mathlib.Analysis.SpecialFunctions.Pow.Complex\npublic import Mathlib.Data.Multiset.Functor\npublic import Mathlib.NumberTheory.NumberField.Basic\npublic import Mathlib.RingTheory.Ideal.Norm.AbsNorm\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl\nimport Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary\nimport Formalism.ConjugateSelfDual.Statement\nimport Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc\nimport ReciprocityTheory.GaloisValuations.GlobalA\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryStringForcesLongPart =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmGaloisRepresentationOfHyp =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmGaloisRepresentationOfHyp", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasString\npublic import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel\npublic import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb\npublic import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete\npublic import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal\npublic import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices\npublic import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs\npublic import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableTrivChar\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmGaloisRepresentationCrystallineStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologicalLocalComponentExponentsStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonModel\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatGLOfIsCompAlongSplit\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSphericalOfIsCompAlongSplit\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeLinearFactorsRegroup\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpehInfMapSubEqSumTwists\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpehPartIsRun\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryStringForcesLongPart\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeSpehOfDiscreteSeries\nimport Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GalAut

noncomputable def shiftF (n d k : ℕ) : ℂ := ((n : ℂ) - 1) / 2 + (((d : ℂ) - 1) / 2 - (k : ℂ))

theorem cast_floor_re {u : ℂ} {j : ℤ} (h : u = j) : ((⌊u.re⌋ : ℤ) : ℂ) = u := by
  rw [h]; simp

theorem mem_spehInf {d : ℕ} {M : Multiset ℂ} {z : ℂ} (hz : z ∈ M) {k : ℕ} (hk : k < d) :
    z + (((d : ℂ) - 1) / 2 - (k : ℂ)) ∈ spehInf d M := by
  unfold spehInf
  refine Multiset.mem_of_le (List.le_sum_of_mem (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩)) ?_
  exact Multiset.mem_map.2 ⟨z, hz, rfl⟩

theorem int_of_mem_infOfWeight {n : ℕ} {lam : DomWeight n} {x : ℂ} (hx : x ∈ infOfWeight lam) :
    ∃ j : ℤ, ((n : ℂ) - 1) / 2 - x = j := by
  obtain ⟨k, -, rfl⟩ := Multiset.mem_map.1 hx
  exact ⟨(k : ℤ) - lam.w k, by push_cast; ring⟩

theorem le_sum_spehInf {c : ℕ} (d : Fin c → ℕ) (M : Fin c → Multiset ℂ) (i : Fin c) :
    spehInf (d i) (M i) ≤ ∑ j, spehInf (d j) (M j) :=
  Finset.single_le_sum (f := fun j => spehInf (d j) (M j)) (fun _ _ => Multiset.zero_le _) (Finset.mem_univ i)

theorem charpoly_eq_of_one {K : Type} [CommRing K] {N : ℕ} (hN : N = 1) (M : Matrix (Fin N) (Fin N) K) :
    M.charpoly = Polynomial.X - Polynomial.C M.det := by
  subst hN
  rw [Matrix.det_fin_one]
  ext k
  simp [Matrix.charpoly]

theorem lift_eq (T : Multiset ℂˣ) :
    (T.map (fun z : ℂ => z) : Multiset ℂ) = T.map (fun z : ℂˣ => (z : ℂ)) := by
  simp only [Multiset.map_id']
  induction T using Multiset.induction_on with
  | empty => rfl
  | cons x s ih => simp_all

end GlobalTheory.GalAut

namespace GlobalTheory.GalAut

theorem map_cast_sum {ι' : Type} [Fintype ι'] (f : ι' → Multiset ℤ) :
    (∑ j, f j).map (fun k : ℤ => (k : ℂ)) = ∑ j, (f j).map (fun k : ℤ => (k : ℂ)) :=
  map_sum (Multiset.mapAddMonoidHom fun k : ℤ => (k : ℂ)) f Finset.univ

theorem map_sub_sum {ι' : Type} [Fintype ι'] (f : ι' → Multiset ℂ) (e : ℂ) :
    (∑ j, f j).map (fun z => e - z) = ∑ j, (f j).map (fun z => e - z) :=
  map_sum (Multiset.mapAddMonoidHom fun z : ℂ => e - z) f Finset.univ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n c : ℕ} {π : Submodule ℂ (UA E n → ℂ)} {a d : Fin c → ℕ}
  {h : ∑ i, d i * a i = n} {P : ∀ i, CuspSub E (a i)} {ρ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (a i)}
  {m : Fin c → (E →+* ℂ) → Multiset ℂ}

theorem int_of_parts (hP : GlobalTheory.BcSpeh.Parts π a d h P ρ m) {τ : E →+* ℂ} {lam : DomWeight n}
    (hl : HasWeightAt π τ lam) (i : Fin c) {z : ℂ} (hz : z ∈ m i τ) {k : ℕ} (hk : k < d i) :
    ∃ j : ℤ, ((n : ℂ) - 1) / 2 - (z + (((d i : ℂ) - 1) / 2 - (k : ℂ))) = j := by
  apply int_of_mem_infOfWeight (lam := lam)
  rw [← hP.weight τ lam hl]
  exact Multiset.mem_of_le (le_sum_spehInf d (fun j => m j τ) i) (mem_spehInf hz hk)

theorem nodup_of_parts (hP : GlobalTheory.BcSpeh.Parts π a d h P ρ m) {τ : E →+* ℂ} {lam : DomWeight n}
    (hl : HasWeightAt π τ lam) (i : Fin c) : (m i τ).Nodup := by
  have h1 : (infOfWeight lam).Nodup := nodup_infOfWeight lam
  rw [← hP.weight τ lam hl] at h1
  have h2 := Multiset.nodup_of_le (le_sum_spehInf d (fun j => m j τ) i) h1
  have h3 : (m i τ).map (· + (((d i : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ))) ≤ spehInf (d i) (m i τ) := by
    unfold spehInf
    exact List.le_sum_of_mem (List.mem_map.2 ⟨0, List.mem_range.2 (hP.pos i).2, rfl⟩)
  exact (Multiset.nodup_of_le h3 h2).of_map _

theorem int_shift (hP : GlobalTheory.BcSpeh.Parts π a d h P ρ m) {τ : E →+* ℂ} {lam : DomWeight n}
    (hl : HasWeightAt π τ lam) (i : Fin c) (k : Fin (d i)) {z : ℂ} (hz : z ∈ m i τ) :
    ∃ j : ℤ, shiftF n (d i) k - z = j := by
  obtain ⟨j, hj⟩ := int_of_parts hP hl i hz (k := d i - 1 - k) (by omega)
  refine ⟨j, ?_⟩
  rw [← hj, shiftF]
  have : ((d i - 1 - (k : ℕ) : ℕ) : ℂ) = (d i : ℂ) - 1 - (k : ℂ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by have := (hP.pos i).2; omega)]; simp
  rw [this]; ring

end GlobalTheory.GalAut

namespace GlobalTheory.GalAut

theorem crystallineHodgeTate_det_rankOne {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {N : ℕ}
    (hN : N = 1) (r : G E Ω →* GL (Fin N) (Qbar l)) (J : (E →+* Qbar l) → Multiset ℤ)
    (hr : GlobalTheory.ExpFrame.CrysWith r J) : GlobalTheory.ExpFrame.CrysWith (GlobalTheory.TripleGal.rk1 (Matrix.GeneralLinearGroup.det.comp r)) J := by
  subst hN
  have : GlobalTheory.TripleGal.rk1 (Matrix.GeneralLinearGroup.det.comp r) = r := by
    ext g i j
    fin_cases i; fin_cases j
    simp [GlobalTheory.TripleGal.rk1]
  rwa [this]

end GlobalTheory.GalAut

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmGaloisRepresentationOfHyp =====
