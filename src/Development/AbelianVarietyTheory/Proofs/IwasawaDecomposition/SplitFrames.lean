module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.JointCharacters.LocEMulLocE
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedLocW
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.SymplecticTensorMeasures
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.WeilIdempotents

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.MainNotions.KudlaSiegelWeil (Pl FinF FinE FF Over Split LocW Restr IntV)
open GlobalTheory.IndefiniteRowSideFullHecke.SymplecticTensorMeasures (ConjIsom basConj omTens toHom)
open Formalism.IndefR.Datum (IsHalf IsLatVac)
open scoped TensorProduct Classical

namespace GlobalTheory.LocWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def idem (D : D7) : Pl D → AE D
  | .inl v => GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.idemFin D v
  | .inr τ => GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.idemInf D (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)))

theorem idem_mul_self (v : Pl D) : idem D v * idem D v = idem D v := by
  rcases v with v | τ
  · simp only [idem, GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.idemFin]
    rw [← map_mul]
    congr 1
    refine Prod.ext (mul_zero _) ?_
    change singleV D.host.F v 1 * singleV D.host.F v 1 = singleV D.host.F v 1
    refine DFunLike.ext _ _ fun u => ?_
    change evalV D.host.F u (singleV D.host.F v 1 * singleV D.host.F v 1) = evalV D.host.F u (singleV D.host.F v 1)
    rw [map_mul]
    by_cases h : u = v
    · subst h
      have : evalV D.host.F u (singleV D.host.F u 1) = 1 := RestrictedProduct.single_eq_same
        (fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletionIntegers D.host.F) u 1
      rw [this, mul_one]
    · have : evalV D.host.F u (singleV D.host.F v 1) = 0 := RestrictedProduct.single_eq_of_ne
        (fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletionIntegers D.host.F) 1 h
      rw [this, mul_zero]
  · simp only [idem, GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.idemInf]
    rw [← map_mul]
    congr 1
    refine Prod.ext ?_ (mul_zero _)
    exact (Pi.single_mul (α := fun w : InfinitePlace D.host.F => w.Completion) _ 1 1).symm.trans (by rw [mul_one]; rfl)

theorem cA_algebraMap (a : AF D.host.F) : cA D (algebraMap (AF D.host.F) (AE D) a) = algebraMap (AF D.host.F) (AE D) a := by
  simp [cA, sigR, Algebra.TensorProduct.algebraMap_apply]

theorem cA_idem (v : Pl D) : cA D (idem D v) = idem D v := by
  rcases v with v | τ <;> exact cA_algebraMap _

instance (θ : InfF D) (V : HSp D) (A : CptF V) : ∀ v, Monoid (Hloc θ V A v)
  | .inl v => inferInstanceAs (Monoid (GAt V (.inl v)))
  | .inr τ => inferInstanceAs (Monoid (HAlg θ V A τ))

variable {X : ThetaX D} {T : ThetaTied D X}

attribute [instance] PairData.sA PairData.sM

end GlobalTheory.LocWeil

end
