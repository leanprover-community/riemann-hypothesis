import Formalism.SharpRestriction.GrowthBounds.LatticeSystems
import Formalism.LocalToGlobal.GroupLattices.FockModels.OperatorsPreserveLattices
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.BeProp
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.BeWInertOfSigma
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.PadicNormTwoHundredSixteenEqOneOfFiveLe
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.HurwitzSubstituteTwoSeries
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.LocalLevelIsKOneAtT
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.AdmissibleThirdOfSecondEleventh
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SigmaAlg
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.PhNorm
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.GenusOneDatumExistence
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.ExistsWittSeriesInverseFormalGroupIso
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntAsm
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntEasy
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntPull
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntStd
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntBasis
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntTens
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.ThFourIntOf
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.UnitSubstOfLoc
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMFour
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntUnit
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.DegreeLeOfCoeffProdNe
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.JetsModel
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.JetsOrth
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.GenusOneWittExistsOf
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.GlobalOrthonormalBasisFour
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntWeak
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.OneCopyTh1SOfIsom
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.AlgKleinPf
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMIsom
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMConj
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.BlockFourfoldHOneEqHOne
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.ConjugationFixedClosure
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntWAPlaces
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FrLocB

section
namespace Formalism.L2.KerInert

def Adm8All : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (p : ℕ) [Fact p.Prime] (X : Formalism.MainNotions.FormalGroupSystem.Sys p), Formalism.MainNotions.FormalGroupSystem.adm8 D X

theorem admissible_all_levels : Adm8All := fun D _ _ X =>
  ⟨Formalism.MainNotions.G.LatticeSystems.exponent_condition_holds D X.G, (Formalism.L2.G.Model.operators_preserve_lattices D X.G).2⟩

end Formalism.L2.KerInert
end

section
namespace Formalism.L2.KerInert

open Formalism.MainNotions.GL3Theta Formalism.L2.G.Pend

def FactsA : Prop := Sigma.InvAlg ∧ Sigma.SecondEisensteinAlgebraic ∧ EndIntInert ∧ PhNormOKInert

theorem beWInert_ofA (h : FactsA) : BeWInert :=
  beWInert_of_sigma (Sigma.sigmaCurveInert_of h.1 h.2.1) h.2.2.1 h.2.2.2

theorem beProp_ofA (h : FactsA) (D : Formalism.BasicNotions.D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ) (p : ℕ)
    [Fact p.Prime] (g : G1 p) (hLT : LTIso g) (hAt : At D cc δ g) (h5 : 5 ≤ p) (hin : InertK D p)
    (hW : ModelOverW g.lam g.abelian₂ g.C) : Formalism.MainNotions.FormalGroupSystem.BeProp p (beLT hLT) :=
  beta_property_of_weight D cc δ p g hLT hAt h5 hin hW (beWInert_ofA h D p cc δ g hAt h5 hin hW)

theorem admissible_second_of_facts (h : FactsA) (D : Formalism.BasicNotions.D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ) (p : ℕ)
    [Fact p.Prime] (g : G1 p) (hLT : LTIso g) (hAt : At D cc δ g) (h5 : 5 ≤ p) (hin : InertK D p)
    (hW : ModelOverW g.lam g.abelian₂ g.C) (X : Formalism.MainNotions.FormalGroupSystem.Sys p) (Y : Formalism.MainNotions.FormalGroupSystem.Pend X) (hY : Y.be = beLT hLT) :
    Formalism.MainNotions.FormalGroupSystem.adm2c D X Y :=
  admissible_second_at_place D cc δ p g hLT hAt h5 hin hW (beWInert_ofA h D p cc δ g hAt h5 hin hW) X Y hY

theorem admissible_eleventh_of_facts (h : FactsA) (D : Formalism.BasicNotions.D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ) (p : ℕ)
    [Fact p.Prime] (g : G1 p) (hLT : LTIso g) (hAt : At D cc δ g) (h5 : 5 ≤ p) (hin : InertK D p)
    (hW : ModelOverW g.lam g.abelian₂ g.C) (X : Formalism.MainNotions.FormalGroupSystem.Sys p) (Y : Formalism.MainNotions.FormalGroupSystem.Pend X) (hY : Y.be = beLT hLT) :
    Formalism.MainNotions.FormalGroupSystem.adm11 D X Y :=
  Jet.adm11OfBeProp D p X Y (hY ▸ beProp_ofA h D cc δ p g hLT hAt h5 hin hW)

end Formalism.L2.KerInert
end

section
namespace Formalism.L2.KerInert

open Formalism.MainNotions.GL3Theta Formalism.L2.G.Pend

theorem inert_facts_first_hold : FactsA :=
  ⟨Sigma.invAlg', Sigma.secondEisensteinAlgebraic, endomorphisms_integral_inert, phi_norm_inert_prime⟩

theorem admissible_second_inert (D : Formalism.BasicNotions.D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ) (p : ℕ)
    [Fact p.Prime] (g : G1 p) (hLT : LTIso g) (hAt : At D cc δ g) (h5 : 5 ≤ p) (hin : InertK D p)
    (hW : ModelOverW g.lam g.abelian₂ g.C) (X : Formalism.MainNotions.FormalGroupSystem.Sys p) (Y : Formalism.MainNotions.FormalGroupSystem.Pend X) (hY : Y.be = beLT hLT) :
    Formalism.MainNotions.FormalGroupSystem.adm2c D X Y :=
  admissible_second_of_facts inert_facts_first_hold D cc δ p g hLT hAt h5 hin hW X Y hY

theorem admissible_eleventh_inert (D : Formalism.BasicNotions.D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ) (p : ℕ)
    [Fact p.Prime] (g : G1 p) (hLT : LTIso g) (hAt : At D cc δ g) (h5 : 5 ≤ p) (hin : InertK D p)
    (hW : ModelOverW g.lam g.abelian₂ g.C) (X : Formalism.MainNotions.FormalGroupSystem.Sys p) (Y : Formalism.MainNotions.FormalGroupSystem.Pend X) (hY : Y.be = beLT hLT) :
    Formalism.MainNotions.FormalGroupSystem.adm11 D X Y :=
  admissible_eleventh_of_facts inert_facts_first_hold D cc δ p g hLT hAt h5 hin hW X Y hY

end Formalism.L2.KerInert
end

section
namespace Formalism.L2.KerInert

def FactsB : Prop :=
  WeakApprox ∧ UnitSubst ∧ UnitSubstLoc ∧ GlobONB ∧ OneCopyLoc ∧ ThMMTransAlgPrime

theorem intInert_ofB (h : FactsB) : IntInert :=
  intInert_of combination_fact pairing_fact h.1 pullback_torsion pullback_fact (AlgGrP.algFact_of_transPrime h.2.2.2.2.2)
    power_series_linearity pairs_standard_at_p (basisInv_of_unitSubst h.2.1) tensor_matrix_units_fact
    (thFourInt_of h.2.2.2.2.1 (locInv_of h.2.2.1) four_products_from_one h.2.2.2.1 (AlgGrP.algZero_of_transPrime h.2.2.2.2.2))

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem jetsInert_ofB (h : FactsB) (hJ : PhiJetInt) : JetsInert :=
  jetsInert_of_int (intInert_ofB h) (orthBasisExists_of h.2.2.2.1 h.1) hJ

end Formalism.L2.KerInert
end

section
namespace Formalism.L2.KerInert

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem genus_one_witt_exists : GenusOneWittExists := ModelP.genus_one_witt_exists_of (GenusOneDatumExistence.genus_one_datum_exists Sigma.invAlg')

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem unit_substitution_local : UnitSubstLoc :=
  unitSubstLoc_of_model (ModelP.endIntInertAll_of endomorphisms_integral_inert genus_one_witt_exists)
    (ModelP.phNormOKInertAll_of phi_norm_inert_prime endomorphisms_integral_inert genus_one_witt_exists)
    (ModelP.biaddInertAll_of (Dict.biaddInert_of (Sigma.sigmaCurveInert_of Sigma.invAlg' Sigma.secondEisensteinAlgebraic))
      genus_one_witt_exists)

def WeakApproxOrthonormalBasesThetaAlgebraicity : Prop := WAPlaces ∧ OneCopyOrth ∧ IsomONB ∧ ThMMTransAlgPrime

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem factsB_of (h : WeakApproxOrthonormalBasesThetaAlgebraicity) : FactsB :=
  ⟨weakApprox_of h.1, unitSubst_of_loc unit_substitution_local, unit_substitution_local, MMOnb.globONB_of h.2.1,
    oneCopyLoc_of_isom h.2.2.1 (AlgGrP.algZero_of_transPrime h.2.2.2), h.2.2.2⟩

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem integral_inert_of_weakApprox_theta (h : WeakApproxOrthonormalBasesThetaAlgebraicity) : IntInert := intInert_ofB (factsB_of h)

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem jets_inert_of_weakApprox_theta (h : WeakApproxOrthonormalBasesThetaAlgebraicity) (hJ : PhiJetInt) : JetsInert := jetsInert_ofB (factsB_of h) hJ

end Formalism.L2.KerInert
end

section
namespace Formalism.L2.KerInert

def WeakApproxAndOrthonormalBases : Prop := WAPlaces ∧ OneCopyOrth ∧ IsomONB

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem integral_inert_of_weakApprox (h : WeakApproxAndOrthonormalBases) : IntInert :=
  intInert_of combination_fact pairing_fact (weakApprox_of h.1) pullback_torsion pullback_fact AlgP.algebraic_fact_kernels
    power_series_linearity pairs_standard_at_p (basisInv_of_loc unit_substitution_local) tensor_matrix_units_fact
    (thFourInt_of (oneCopyLoc_of_isom h.2.2 AlgP.zero_value_algebraic) (locInv_of unit_substitution_local) four_products_from_one
      (MMOnb.globONB_of h.2.1) AlgP.zero_value_algebraic)

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem jets_inert_of_weakApprox (h : WeakApproxAndOrthonormalBases) (hJ : PhiJetInt) : JetsInert :=
  jetsInert_of_int (integral_inert_of_weakApprox h) (orthBasisExists_of (MMOnb.globONB_of h.2.1) (weakApprox_of h.1)) hJ

end Formalism.L2.KerInert
end

section
namespace Formalism.L2.KerInert

theorem isomONB_ofLB (hLB : LocBasisMM) : IsomONB :=
  isomONB_of_facts conjugation_extension_inert hLB rational_coordinates conjugation_fixed_closure

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in

theorem integral_inert_of_approx_basis (hWA : WAPlaces) (hLB : LocBasisMM) : IntInert :=
  integral_inert_of_weakApprox ⟨hWA, one_theta_orthonormal, isomONB_ofLB hLB⟩

end Formalism.L2.KerInert
end

section
namespace Formalism.L2.KerInert

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in

theorem kernels_integral_inert : IntInert := integral_inert_of_approx_basis weak_approximation_places local_orthonormal_basis

end Formalism.L2.KerInert
end
