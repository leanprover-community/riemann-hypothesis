module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIotaOQOfDataStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGaloisRepDecompositionInduced
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfWdMkPhiDPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteIsNilpotentOfUnipotent
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KummerNotFrac
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPotentiallySemistableCoefficientFieldEnlargeStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficieStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankDpstUnramifiedLeDimRepresentationStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DpstRankLeDimension
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotSemistableOfPotCrystallineDecompositionGroupStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharPolyInertiaOfPotSemistableEnlargementStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalInertiaEqZeroPotSemistableDieudonneStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalKillsPotCrystallineOfKillsPotSemistableStatement

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open TensorProduct

namespace GlobalTheory.KillLocal

theorem actPow {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) (g : G) (n : ℕ) (x : V ⊗[Qp] B) :
    actVB PD ρ (g ^ n) x = (actVB PD ρ g ^ n) x := by
  induction n generalizing x with
  | zero =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVB]
    | add a b ha hb => rw [map_add (f := _), ha, hb, map_add (f := _)]
  | succ n ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, ← ih]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVB, map_mul, AlgEquiv.mul_apply]
    | add a b ha hb => rw [map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]

theorem sumAeval {O LL M : Type} [CommRing O] [Field LL] [AddCommGroup M] [Module LL M] (f : O →+* LL)
    (T : Module.End LL M) (p : O[X]) (x : M) :
    ∑ n ∈ Finset.range (p.natDegree + 1), f (p.coeff n) • (T ^ n) x = Polynomial.aeval T (p.map f) x := by
  rw [Polynomial.aeval_eq_sum_range' (n := p.natDegree + 1) (Nat.lt_succ_of_le Polynomial.natDegree_map_le)]
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, Polynomial.coeff_map]

end GlobalTheory.KillLocal
