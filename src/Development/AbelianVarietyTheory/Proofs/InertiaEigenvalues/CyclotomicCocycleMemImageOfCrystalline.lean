module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueFits
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWachImageIsClosedStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Xstab
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZgFormula
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

namespace GlobalTheory.NL.ZVal

private theorem add_coboundary {G M : Type} [Mul G] [AddCommGroup M]
    (a : G → M →+ M) (u : G → M) (b : M) (g g' : G)
    (ha : a (g * g') b = a g (a g' b))
    (hu : u (g * g') = u g + a g (u g')) :
    u (g * g') + (a (g * g') b - b) =
      (u g + (a g b - b)) + a g (u g' + (a g' b - b)) := by
  rw [ha, hu, map_add (a g), map_sub (a g)]
  abel

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem zval : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL), IsCrys ((D.loc l).PD K) T.ρ → ∀ (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (b : TW (RW LL) T) (lam : ↥((HW l).W K s LL h).GKs →* Multiplicative ℤ_[l]), Continuous lam → (∀ g, lam g = 1 → ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1) → (∀ g : ↥((HW l).W K s LL h).GKs, ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1 → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g = 0) → ∀ g₁ : ↥((HW l).W K s LL h).GKs, lam g₁ = Multiplicative.ofAdd 1 → ∀ z₁ ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X, Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g₁ = ((F l).E K s LL h).tie.jD T z₁ → ∀ g : ↥((HW l).W K s LL h).GKs, ∃ z ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X, Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g = ((F l).E K s LL h).tie.jD T z := by
  intro D HW F l _ K s LL h T hT c b lam hlc hl1 hZk g₁ hg₁ z₁ hz₁ hZ₁
  -- Reuse the algebra instances needed for the lattice and its tensor products.
  let _ : Algebra ℚ_[l] ↥LL.1 := inferInstance
  let _ : Algebra ↥(OL LL) ↥LL.1 := inferInstance
  let _ : Algebra ↥(OL LL) (RW LL) := inferInstance
  let _ : Algebra ↥(OL LL) (RA LL) := inferInstance
  let _ : Module ↥(OL LL) (RW LL) := Algebra.toModule
  let _ : Module ↥(OL LL) ↥T.L.T := T.modT
  let W := (HW l).W K s LL h
  let E := ((F l).E K s LL h).tie
  let H := W.GKs
  let M := TW (RW LL) T
  let mGroup : AddCommGroup M := TensorProduct.addCommGroup
  let _ : AddGroup M := mGroup.toAddGroup
  let _ : Sub M := mGroup.toAddGroup.toSubNegMonoid.toSub
  let N := aN W T W.X
  let j := (E.jD T).toAddMonoidHom
  let Z := Zf (D.locA l) T H c b
  have hc := GlobalTheory.HerrClassMaps.compact_GK K
  have hcl : IsClosed (H : Set ↥(GK K)) :=
    (lam_exists D HW K s LL h).elim fun _ hx => hx.2.2.2.2
  have hcs : CompactSpace ↥H := isCompact_iff_compactSpace.1 hcl.isCompact
  refine (GlobalTheory.T.exists_weakTopology_wachImage_isClosed D HW F l K s LL h T hT).elim fun τ hτ => ?_
  let _ : TopologicalSpace M := τ
  have hT2 : T2Space M := hτ.1
  have hTG : IsTopologicalAddGroup M := hτ.2.1
  have hact := hτ.2.2.1
  have hemb := hτ.2.2.2.1
  have hclo := hτ.2.2.2.2
  let r := (D.locA l).gRW LL
  let a : ↥H → M →+ M := fun g => (TWact (r (g.1 : GQ l)) T g.1).toAddMonoidHom
  have hmul (g g' : ↥H) : a (g * g') b = a g (a g' b) :=
    GlobalTheory.HerrClassMaps.TWact_mul
      (r ((g * g').1 : GQ l)) (r (g.1 : GQ l)) (r (g'.1 : GQ l))
      (GlobalTheory.HerrClassMaps.gRW_mul (D.locA l) LL (g.1 : GQ l) (g'.1 : GQ l))
      T g.1 g'.1 b
  have haj (g : ↥H) (w : W.DD T) : a g (j w) = j (W.γD T (W.resΓ g.1) w) :=
    (E.jD_act T g.1 w).symm
  let J := N.toAddSubgroup.map j
  have hJm (x : M) : x ∈ J ↔ ∃ w ∈ N, j w = x := Iff.rfl
  have hJ : IsClosed (J : Set M) := hclo
  have hJa (g : ↥H) (x : M) (hx : x ∈ J) : a g x ∈ J :=
    ((hJm x).1 hx).elim fun w hw =>
      (hJm _).2 ⟨_, GlobalTheory.NL.XStab.xstab D HW l K s LL h T _ w hw.1,
        (haj g w).symm.trans (congrArg (fun y => a g y) hw.2)⟩
  have hJk (g : ↥H) (hg : lam g = 1) (x : M) (hx : x ∈ J) : a g x = x :=
    ((hJm x).1 hx).elim fun w hw => calc
      a g x = a g (j w) := congrArg (fun y => a g y) hw.2.symm
      _ = j (W.γD T (W.resΓ g.1) w) := haj g w
      _ = j (W.γD T 1 w) := congrArg (fun δ => j (W.γD T δ w)) (hl1 g hg)
      _ = j w := congrArg (fun y => j y) (W.γD_one T w)
      _ = x := hw.2
  have hCA : ContinuousAdd M := hTG.toContinuousAdd
  have hCS : ContinuousSub M := @IsTopologicalAddGroup.to_continuousSub M τ mGroup.toAddGroup hTG
  let liftC : ↥H → ↥T.L.T := fun g => ⟨c.1 g, c.2.2 g (Set.mem_univ g)⟩
  have hLiftC : Continuous liftC :=
    c.2.1.1.subtype_mk fun g => (liftC g).2
  have hZc : Continuous Z :=
    Continuous.add (M := M) (hemb.comp hLiftC)
      (Continuous.sub (G := M) ((hact b).comp continuous_subtype_val) continuous_const)
  let k : ↥T.L.T → M := fun t => (1 : RW LL) ⊗ₜ[↥(OL LL)] t
  have ha1t (g : ↥H) (t : ↥T.L.T) : a g (k t) = k (T.actT g.1 t) :=
    GlobalTheory.HerrClassMaps.TWact_one_tmul (r (g.1 : GQ l)) T g.1 t
  have hLiftMul (g g' : ↥H) : liftC (g * g') = liftC g + T.actT g.1 (liftC g') :=
    Subtype.ext (c.2.1.2 g g')
  have hZm (g g' : ↥H) : Z (g * g') = Z g + a g (Z g') :=
    add_coboundary a (fun g => k (liftC g)) b g g' (hmul g g') (calc
      k (liftC (g * g')) = k (liftC g + T.actT g.1 (liftC g')) :=
        congrArg (fun t => k t) (hLiftMul g g')
      _ = k (liftC g) + k (T.actT g.1 (liftC g')) :=
        TensorProduct.tmul_add (R := ↥(OL LL)) (1 : RW LL) _ _
      _ = k (liftC g) + a g (k (liftC g')) :=
        congrArg (fun x => k (liftC g) + x) (ha1t g (liftC g')).symm)
  have hZk' (g : ↥H) (hg : lam g = 1) : Z g = 0 := hZk g (hl1 g hg)
  have hzJ : j z₁ ∈ J := (hJm _).2 ⟨z₁, hz₁, rfl⟩
  have HM := (GlobalTheory.NL.ZgAll.mem_and_comm a lam hlc g₁ hg₁ J hJ hJa hJk _ hzJ
    Z hZc hZm hZk' hZ₁).1
  intro g
  exact ((hJm _).1 (HM g)).elim fun w hw => ⟨w, hw.1, hw.2.symm⟩

end GlobalTheory.NL.ZVal
