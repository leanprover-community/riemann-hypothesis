module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullAutConst

theorem main : ∀ {A : Type} [CommRing A] (B' : Over (Sp A)) [GrpObj B'] {X : Scheme.{0}} (L : LB X) (π : B'.left ⟶ X), IsAbelianScheme B' → L.IsLB → ∀ w : LB.Iso (L.pull π) (L.pull π), w.IsGen → ∃ lam : Aˣ, ∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (z : Z) (j : L.ι), π (x z) ∈ L.U j → gm x z _ (w.s (fun _ => j, fun _ => j)) = gm (x ≫ B'.hom) z ⊤ (unitOn lam) := by
  intro A _ B' _ X L π hB hL w hw
  have hP := (isGen_iff w).1 hw
  have hg : ∀ (j j' : L.ι) (x : B'.left), π x ∈ L.U j → π x ∈ L.U j' →
      gm (𝟙 B'.left) x _ ((L.pull π).g (fun _ => j) (fun _ => j')) = gm (𝟙 _ ≫ π) x _ (L.g j j') := by
    intro j j' x hj hj'
    have hp : (𝟙 B'.left : B'.left ⟶ B'.left) x ∈ (L.pull π).U (fun _ => j) ⊓ (L.pull π).U (fun _ => j') :=
      ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
    show gm _ x _ (∏ _k : PUnit, (res _ (pullU π _ (L.g j j'))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    exact (gm_res _ x _ hp _).trans (gm_pull _ π x (L.U j ⊓ L.U j') ⟨hj, hj'⟩ _)
  obtain ⟨u, hu⟩ := glue_unit (⊤ : B'.left.Opens)
    (fun j : L.ι => (L.pull π).U (fun _ => j) ⊓ (L.pull π).U (fun _ => j)) (fun _ => le_top)
    (fun x _ => by
      obtain ⟨j, hj⟩ := exists_chart hL (π x)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, mem_pull.2 hj, mem_pull.2 hj⟩)
    (fun j => w.s (fun _ => j, fun _ => j)) (fun j j' x hx => by
      have hj : π x ∈ L.U j := mem_pull.1 hx.1.1
      have hj' : π x ∈ L.U j' := mem_pull.1 hx.2.1
      have e := hP _ (𝟙 _) x j j' (fun _ => j) (fun _ => j') hj hj' (mem_pull.2 hj) (mem_pull.2 hj')
      rw [hg j j' x hj hj', mul_inv_cancel] at e
      exact e.trans (_root_.one_mul _))
  let e₁ : Γ(Sp A, ⊤) ≃+* Γ(B'.left, ⊤) :=
    RingEquiv.ofBijective B'.hom.appTop.hom (GlobalTheory.globalFns_holds _ B' hB)
  let e₂ : A ≃+* Γ(Sp A, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv
  let e : A ≃+* Γ(B'.left, ⊤) := e₂.trans e₁
  refine ⟨Units.map e.symm.toMonoidHom u, fun Z x z j hj => ?_⟩
  have hl : pullU B'.hom ⊤ (unitOn (Units.map e.symm.toMonoidHom u)) = u :=
    Units.ext (e.apply_symm_apply u.val)
  have hm : x z ∈ (L.pull π).U (fun _ => j) ⊓ (L.pull π).U (fun _ => j) := ⟨mem_pull.2 hj, mem_pull.2 hj⟩
  refine (congrArg (gm x z _) (hu j)).symm.trans ((gm_res x z _ hm _).trans ?_)
  exact (congrArg (gm x z ⊤) hl).symm.trans (gm_pull x B'.hom z ⊤ trivial _)

end GlobalTheory.PullAutConst
