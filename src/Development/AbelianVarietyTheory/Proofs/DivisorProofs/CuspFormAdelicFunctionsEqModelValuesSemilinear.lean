module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertModelExtremalValuesEqHolomorphicCuspFormsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IpMSelfEqZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspFormValues

theorem evEx_of_range {K C H X : Type} [Field K] [AddCommGroup C] [Module K C] [AddCommGroup H] [Module ℂ H]
    [AddCommGroup X] [Module ℂ X] (σ : K →+* ℂ) (ev : H → X) (φ : C → X) (hinj : Function.Injective ev)
    (hadd : ∀ x y, ev (x + y) = ev x + ev y) (hsmul : ∀ (a : ℂ) x, ev (a • x) = a • ev x)
    (hφa : ∀ f g, φ (f + g) = φ f + φ g) (hφs : ∀ (a : K) f, φ (a • f) = σ a • φ f)
    (hmem : ∀ f, φ f ∈ Set.range ev) : EvEx σ ev φ := by
  choose j hj using hmem
  exact ⟨{ toFun := j
           map_add' := fun f g => hinj (by rw [hadd, hj, hj, hj, hφa])
           map_smul' := fun a f => hinj (by rw [hsmul, hj, hj, hφs]) }, hj⟩

theorem phiC_eq {D : D7} (T : CoreJ D) {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) :
    phiC T hV a f = adel W (castDict hV (T.dict j σ)) (muPin W (castDict hV (T.dict j σ)) (castDict hV (T.mu j σ)) (T.cE j σ))
      ((lieFac (T.Q.Dw j) (xiR D) a : ℂ) • rdU (T.U j σ) f) := by
  subst hV
  rw [map_smul]
  rfl

theorem jEvExists : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → JEvExists T R κ v₀ := by
  intro hdec hvol D G _ _ Pl0 T0 A T _ R κ v₀ hlev hmod htie hpb i σ hσ hV
  have hr := GlobalTheory.T.hilbertModel_extremalValues_eq_holomorphicCuspForms hdec hvol D G Pl0 T0 A T R κ v₀ hlev hmod htie hpb i σ hσ hV
  refine evEx_of_range _ _ _ (GlobalTheory.EvalAtUnitVector.evInj T R v₀ hmod.HW htie.hv₀ i σ hσ) (fun x y => ?_) (fun a x => ?_)
    (fun f g => ?_) (fun a f => ?_) (fun f => ?_)
  · unfold evAt
    rw [map_add (f := _)]
    rfl
  · unfold evAt
    rw [map_smul]
    rfl
  · simp only [phiC_eq]
    rw [Submodule.coe_add, map_add (f := _), smul_add, map_add (f := _)]
  · simp only [phiC_eq]
    rw [Submodule.coe_smul, map_smulₛₗ (rdU _), smul_comm, map_smul]
  · rw [hr, phiC_eq]
    exact ⟨_, Submodule.smul_mem _ _
      (Submodule.mem_inf.2 ⟨((mem_cusp _ _ _ _ _ _).1 f.2).2 _ hσ, rdU_mem_offZero _ _⟩), rfl⟩

end GlobalTheory.CuspFormValues
