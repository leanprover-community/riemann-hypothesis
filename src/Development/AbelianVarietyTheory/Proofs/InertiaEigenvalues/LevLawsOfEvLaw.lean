module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ApplyLayers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgHomExtOfConstantCoeffZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysLatOfTrivial
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBinomial

@[expose] public section

noncomputable section

namespace GlobalTheory.NL

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL PowerSeries

section Generic

variable {l : ℕ} [Fact l.Prime] {O L : Type} [CommRing O] [Field L] [CharZero L] [Algebra ℚ L] [Algebra ℤ_[l] O]
    [Algebra ℤ_[l] L] [Algebra O L] [IsScalarTower ℤ_[l] O L] {v : AddValuation L (WithTop ℚ)}
    {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR}
    [Algebra Qp L] [TopologicalSpace L] {n : ℕ}

end Generic

section Concrete

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (H : LocHW l P) (F : LocFon l P AI H)
  {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL)

theorem one_crys : IsCrys (P.PD K) (H.W K s LL h).one.ρ :=
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  GlobalTheory.TrivCrys.isCrys_lat_of_trivial _ (H.W K s LL h).one_triv

end Concrete

end GlobalTheory.NL
