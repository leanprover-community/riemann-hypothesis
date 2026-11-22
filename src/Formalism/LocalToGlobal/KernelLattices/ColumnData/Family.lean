module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.ColumnData
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CardTrivialFirstComponent
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
public import Development.AutomorphicArithmetic.WeightCongruences.IsRootOfIntegral
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.LinkThU
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ThIndep

@[expose] public section

noncomputable section

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Formalism.L2.Ker Classical
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

def LinkBaseNe : Prop :=
  ∀ (D : Car) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Base D cc δ → δ ≠ 0

theorem lamOf_zero (D : Car) (cc : Ideal (𝓞 D.host.K)) : lamOf D cc 0 = ⊥ := by
  unfold lamOf
  rw [AddSubgroup.closure_eq_bot_iff]
  rintro w ⟨c, -, rfl⟩
  simp

theorem base_linkage_nonempty : LinkBaseNe := by
  intro D cc δ B h0
  subst h0
  have h1 : B.L.ω₁ ∈ B.L.lattice.toAddSubgroup := B.L.ω₁_mem_lattice
  rw [B.lat, lamOf_zero, AddSubgroup.mem_bot] at h1
  have h2 := B.L.indep.ne_zero 0
  exact h2 (by simpa using h1)

end Formalism.L2.Ker.Cd.IntegralLatticeDensity

end
