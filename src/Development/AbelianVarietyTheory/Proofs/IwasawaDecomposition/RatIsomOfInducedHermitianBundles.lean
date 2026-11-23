module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
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
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtAlgebraMap

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.InducedIsom

open OfModel

theorem isRatSec_lift {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z] (j : Z ⟶ X)
    (ρ : X.functionField ≃+* Z.functionField)
    (hρ : ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (hU' : genericPoint Z ∈ j ⁻¹ᵁ U) (s : Γ(X, U)),
      ρ (fnOf U hU s) = fnOf (j ⁻¹ᵁ U) hU' (j.app U s))
    (hj : j (genericPoint Z) = genericPoint X) (B : LB X) {r : (B.pull j).ι → Z.functionFieldˣ}
    (hr : IsRatSec (B.pull j) r) :
    IsRatSec B fun i => Units.map ρ.symm.toMonoidHom (r fun _ => i) := by
  intro i i' h
  have h' : genericPoint Z ∈ j ⁻¹ᵁ (B.U i ⊓ B.U i') := by
    change j (genericPoint Z) ∈ B.U i ⊓ B.U i'
    rwa [hj]
  have h₂ : genericPoint Z ∈ (B.pull j).U (fun _ => i) ⊓ (B.pull j).U (fun _ => i') :=
    ⟨Set.mem_iInter.2 fun _ => h'.1, Set.mem_iInter.2 fun _ => h'.2⟩
  have l : (B.pull j).U (fun _ => i) ⊓ (B.pull j).U (fun _ => i') ≤ j ⁻¹ᵁ (B.U i ⊓ B.U i') :=
    fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have hg : ((B.pull j).g (fun _ => i) (fun _ => i')).val = resG Z l (j.app _ (B.g i i').val) := by
    have : (B.pull j).g (fun _ => i) (fun _ => i') = res l (pullU j _ (B.g i i')) := by
      change ∏ _k : PUnit, _ = _
      exact (Fintype.prod_unique _).trans (zpow_one _)
    rw [this]
    rfl
  have e := hr (fun _ => i) (fun _ => i') h₂
  rw [hg, fnOf_resG, ← hρ _ h] at e
  apply ρ.injective
  rw [map_mul]
  exact (ρ.apply_symm_apply _).trans (e.trans (congrArg _ (ρ.apply_symm_apply _).symm))

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F}

end GlobalTheory.TrueGeo.InducedIsom
