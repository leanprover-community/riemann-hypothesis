module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToNatLengthEqRangeAddRange
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PullbackAndTensorModule
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRigidifiedIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormalTwistingNeTrivial, Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RestrictionPoincareBundle

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormalTwistingNeTrivial =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormalTwistingNeTrivial", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ToNatLengthEqRangeAddRange\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CechPic GlobalTheory.Vert

namespace GlobalTheory.FormalPic

variable {X : ℕ → Scheme.{0}} (i : ∀ e, X e ⟶ X (e + 1))

structure FLB : Type 1 where

  ι : Type

  U : ∀ e, ι → (X e).Opens

  g : ∀ e a b, Γ(X e, U e a ⊓ U e b)ˣ
  isLB : ∀ e, LB.IsLB ⟨ι, U e, g e⟩
  U_eq : ∀ e a, U e a = i e ⁻¹ᵁ U (e + 1) a
  g_eq : ∀ e a b, g e a b = res (U := i e ⁻¹ᵁ (U (e + 1) a ⊓ U (e + 1) b))
    (le_inf (inf_le_left.trans (U_eq e a).le) (inf_le_right.trans (U_eq e b).le)) (pullU (i e) _ (g (e + 1) a b))

variable {i}

namespace FLB

abbrev lb (L : FLB i) (e : ℕ) : LB (X e) := ⟨L.ι, L.U e, L.g e⟩

def Compat {L M : FLB i} (u : ∀ e, LB.Iso (L.lb e) (M.lb e)) : Prop :=
  ∀ e (p : M.ι × L.ι), (u e).s p = res (U := i e ⁻¹ᵁ (M.U (e + 1) p.1 ⊓ L.U (e + 1) p.2))
    (le_inf (inf_le_left.trans (M.U_eq e p.1).le) (inf_le_right.trans (L.U_eq e p.2).le)) (pullU (i e) _ ((u (e + 1)).s p))

def Iso (L M : FLB i) : Prop := ∃ u : ∀ e, LB.Iso (L.lb e) (M.lb e), (∀ e, (u e).IsGen) ∧ Compat u

def reindex (L : FLB i) {κ : Type} (j : κ → L.ι) (h : ∀ e (x : X e), ∃ k, x ∈ L.U e (j k)) : FLB i where
  ι := κ
  U e k := L.U e (j k)
  g e k l := L.g e (j k) (j l)
  isLB e := ⟨top_le_iff.1 fun x _ => Opens.mem_iSup.2 (h e x), fun _ => (L.isLB e).g_self _,
    fun _ _ _ => (L.isLB e).cocycle _ _ _⟩
  U_eq e k := L.U_eq e (j k)
  g_eq e k l := L.g_eq e (j k) (j l)

instance setoid : Setoid (FLB i) := ⟨Iso, Iso.refl, Iso.symm, Iso.trans⟩

variable {Y Y' : Scheme.{0}} (q : ∀ e, X e ⟶ Y) (hq : ∀ e, i e ≫ q (e + 1) = q e)

def ofPull (L : LB Y) (hL : L.IsLB) : FLB i :=
  have hU : ∀ e (a : PUnit → L.ι), (L.pull (q e)).U a = i e ⁻¹ᵁ (L.pull (q (e + 1))).U a := fun e a => by
    ext x
    refine mem_pull.trans (Iff.trans ?_ (mem_pull (F := q (e + 1)) (x := i e x)).symm)
    rw [← hq e]; rfl
  { ι := PUnit → L.ι
    U e := (L.pull (q e)).U
    g e := (L.pull (q e)).g
    isLB e := pull_isLB hL (q e)
    U_eq := hU
    g_eq e a b := (eq_res_pullU_iff _ _ _ _).2 fun x hx => by
      refine (gm_pull_g L (q e) (𝟙 _) x a b hx.1 hx.2).trans
        (Eq.trans ?_ (gm_pull_g L (q (e + 1)) (i e) x a b ((hU e a).le hx.1) ((hU e b).le hx.2)).symm)
      rw [Category.id_comp, hq] }

theorem ofPull_iso {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (h : LBIso A B) : (ofPull q hq A hA).Iso (ofPull q hq B hB) :=
  iso_of_chartPull q (fun J => J ⟨⟩) (fun J => J ⟨⟩) (fun _ _ _ hx => mem_pull.1 hx) (fun _ _ _ hx => mem_pull.1 hx)
    (fun e x k l hk hl => (Geo.Tor.chartPullPull A (q e) (q e) rfl).g x k l hk hl)
    (fun e x k l hk hl => (Geo.Tor.chartPullPull B (q e) (q e) rfl).g x k l hk hl) hq h

end FLB

variable (i) in
structure FLBOn (κ : Type) : Type where

  U : ∀ e, κ → (X e).Opens

  g : ∀ e a b, Γ(X e, U e a ⊓ U e b)ˣ
  isLB : ∀ e, LB.IsLB ⟨κ, U e, g e⟩
  U_eq : ∀ e a, U e a = i e ⁻¹ᵁ U (e + 1) a
  g_eq : ∀ e a b, g e a b = res (U := i e ⁻¹ᵁ (U (e + 1) a ⊓ U (e + 1) b))
    (le_inf (inf_le_left.trans (U_eq e a).le) (inf_le_right.trans (U_eq e b).le)) (pullU (i e) _ (g (e + 1) a b))

def FLBOn.toFLB {κ : Type} (L : FLBOn i κ) : FLB i := ⟨κ, L.U, L.g, L.isLB, L.U_eq, L.g_eq⟩

def FLB.toOn (L : FLB i) : FLBOn i L.ι := ⟨L.U, L.g, L.isLB, L.U_eq, L.g_eq⟩

instance small_quotient : Small.{0} (Quotient (FLB.setoid (i := i))) := by
  refine small_of_surjective (α := FLBOn i (Σ e, X e)) (f := fun p => Quotient.mk _ p.toFLB) fun c => ?_
  obtain ⟨L, rfl⟩ := Quotient.exists_rep c
  choose j hj using fun x : Σ e, X e => exists_chart (L.isLB x.1) x.2
  have h : ∀ e (x : X e), ∃ k, x ∈ L.U e (j k) := fun e x => ⟨⟨e, x⟩, hj ⟨e, x⟩⟩
  exact ⟨(L.reindex j h).toOn, Quotient.sound (L.reindex_iso j h)⟩

variable (i) in
def FPic : Type := Shrink.{0} (Quotient (FLB.setoid (i := i)))

def fcls (L : FLB i) : FPic i := equivShrink _ (Quotient.mk _ L)

def level (e : ℕ) (c : FPic i) : SmallPic (X e) :=
  Quotient.lift (s := FLB.setoid) (fun L : FLB i => smallCls (L.lb e) (L.isLB e))
    (fun _ _ h => (smallCls_eq_iff _ _).2 (h.elim fun u hu => ⟨u e, hu.1 e⟩)) ((equivShrink _).symm c)

variable {Y Y' : Scheme.{0}} (q : ∀ e, X e ⟶ Y) (hq : ∀ e, i e ≫ q (e + 1) = q e)

def fpull (c : SmallPic Y) : FPic i :=
  Quotient.lift (s := CechPic.setoid Y) (fun A => fcls (FLB.ofPull q hq A.1 A.2))
    (fun A B h => fcls_eq_iff.2 (FLB.ofPull_iso q hq A.2 B.2 h)) (smallPicEquiv Y c)

section Projective

open GlobalTheory.ProjSpace

variable {R : Type} [CommRing R] (I : Ideal R) (N : ℕ)

end Projective

end GlobalTheory.FormalPic
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormalTwistingNeTrivial =====

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RestrictionPoincareBundle =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RestrictionPoincareBundle", "h": "module\n\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PullbackAndTensorModule\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormalTwistingNeTrivial\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsGrpPullbackAbVarModel\npublic import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRigidifiedIso\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Out (thick thickObj thickMap thickTrans)
open ReciprocityTheory.ChartRestriction.G.Out.PullGtPf (hMap sE)
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.Serre GlobalTheory.CechPic GlobalTheory.HermTensor GlobalTheory.Vert GlobalTheory.FormalPic
open scoped CategoryTheory.Obj

namespace GlobalTheory.LocM

section Classes

variable {S S' : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

def IsRigCls (c : SmallPic G.left) : Prop := smallPull (eSec G) c = 0

def IsSymCls (c : SmallPic G.left) : Prop := smallPull (GrpObj.inv (X := G)).left c = c

def IsPrincipalCls (c : SmallPic G.left) : Prop :=
  ∃ (L : LB G.left) (hL : L.IsLB), smallCls L hL = c ∧ Out.RelAmple G L ∧ Out.KTriv G L

def RigPic : Type := {c : SmallPic G.left // IsRigCls G c}

variable {G}

omit [GrpObj G] [IsCommMonObj G] in
theorem smallCls_eq_zero_iff {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : smallCls L hL = 0 ↔ ∃ t : LB.Gen L, t.IsGen :=
  (smallPicEquiv X).symm.map_eq_zero_iff.trans (cls_eq_zero_iff hL)

omit [GrpObj G] [IsCommMonObj G] in
theorem smallPull_comp {X Y Z : Scheme.{0}} (g : Z ⟶ Y) (f : Y ⟶ X) (c : SmallPic X) :
    smallPull (g ≫ f) c = smallPull g (smallPull f c) := by
  simp [smallPull, pull_comp]

omit [IsCommMonObj G] in
theorem isRigCls_iff {L : LB G.left} (hL : L.IsLB) : IsRigCls G (smallCls L hL) ↔ Out.Rigidified G L := by
  rw [IsRigCls, smallPull_smallCls _ hL (pull_isLB hL _), smallCls_eq_zero_iff]; rfl

def rigCls (L : RigLB G) : RigPic G := ⟨smallCls L.L L.isLB, (isRigCls_iff L.isLB).2 ⟨L.rig, L.rigGen⟩⟩

def IsBiextCls (P : RigPic (G ⊗ G)) : Prop := ∃ L : RigLB (G ⊗ G), rigCls L = P ∧ Nonempty (IsBiext G L.L)

def diagCls (w : G ⟶ G) (P : RigPic (G ⊗ G)) : SmallPic G.left := smallPull (lift (𝟙 G) w).left P.1

variable {G' : Over S'} [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ)

omit [IsCommMonObj G] [IsCommMonObj G'] in
def sqMap : (G' ⊗ G').left ⟶ (G ⊗ G).left := (lift (pushHom h _ (fst G' G')) (pushHom h _ (snd G' G'))).left

omit [IsCommMonObj G] [IsCommMonObj G'] in
@[reassoc] theorem sqMap_snd : sqMap h ≫ (snd G G).left = (snd G' G').left ≫ φ :=
  congrArg (fun q => q.left) (lift_snd (pushHom h _ (fst G' G')) (pushHom h _ (snd G' G')))

omit [GrpObj G] [IsCommMonObj G] in
theorem sq_hom_ext {T : Scheme.{0}} {a b : T ⟶ (G ⊗ G).left} (h₁ : a ≫ (fst G G).left = b ≫ (fst G G).left)
    (h₂ : a ≫ (snd G G).left = b ≫ (snd G G).left) : a = b := pullback.hom_ext h₁ h₂

theorem eSec_sqMap : eSec (G' ⊗ G') ≫ sqMap h = f ≫ eSec (G ⊗ G) := by
  have e : η[G'].left ≫ φ = f ≫ η[G].left := (cubeMapOf h).e_comm
  refine sq_hom_ext ?_ ?_
  · rw [Category.assoc, sqMap_fst, eSec, eSec, ← Over.comp_left_assoc, Category.assoc, ← Over.comp_left,
      IsMonHom.one_hom, IsMonHom.one_hom, e]
  · rw [Category.assoc, sqMap_snd, eSec, eSec, ← Over.comp_left_assoc, Category.assoc, ← Over.comp_left,
      IsMonHom.one_hom, IsMonHom.one_hom, e]

def sqPull (P : RigPic (G ⊗ G)) : RigPic (G' ⊗ G') :=
  ⟨smallPull (sqMap h) P.1, by
    rw [IsRigCls, ← smallPull_comp, eSec_sqMap]
    exact (smallPull_comp _ _ _).trans ((congrArg _ P.2).trans (map_zero _))⟩

theorem smallPull_diagCls {w : G ⟶ G} {w' : G' ⟶ G'} (hw : w'.left ≫ φ = φ ≫ w.left) (P : RigPic (G ⊗ G)) :
    smallPull φ (diagCls w P) = diagCls w' (sqPull h P) := by
  refine (smallPull_comp _ _ _).symm.trans (Eq.trans (congrArg (smallPull · P.1) ?_) (smallPull_comp _ _ _))
  refine sq_hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, sqMap_fst, ← Over.comp_left, ← Over.comp_left_assoc, lift_fst, lift_fst]
    simp
  · rw [Category.assoc, Category.assoc, sqMap_snd, ← Over.comp_left, ← Over.comp_left_assoc, lift_snd, lift_snd, hw]

end Classes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

namespace tens

variable {X X' : Scheme.{0}} (t : SAB H X) (Λ : Unim E)

def ppCls : SmallPic (tens t Λ).G.left := smallCls (tens t Λ).PP.L (tens t Λ).PP.isLB

def poiCls : RigPic ((tens t Λ).G ⊗ (tens t Λ).G) := rigCls (poi t Λ)

def diag (P : RigPic ((tens t Λ).G ⊗ (tens t Λ).G)) : SmallPic (tens t Λ).G.left := diagCls ((tens t Λ).act.act H.w0) P

end tens

section Unif

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)} (U : PELUnif I t) (Λ : Unim E)

def abPartAct : OAct (𝓞 E) U.D.toPre.P.A := letI := H.starRing; ofRingAct U.oD.onB.toRingAct

abbrev abTens : Over (Sp R) := Λ.obj (abPartAct U)

def qTens (e : ℕ) : thickObj R I e (tens t Λ).G ⟶ thickObj R I e (abTens U Λ) :=
  ((tens.isTensor t Λ).pullback (thick R I e)).mapRight ((Λ.isTensor (abPartAct U)).pullback (thick R I e))
    (isLinearHom_q U e)

end Unif

section Point

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β} {p : ℕ} {C : SCF p} {P : PointsOfFlagModel.PtC Y C} (A : DatAt Y P) (Λ : Unim E)

def defIdeal : Ideal ↥(intO ↥C.S) := (maximalIdeal A.R).map A.f

abbrev gPt : Over (Sp ↥(intO ↥C.S)) := (Over.pullback (spMap A.f)).obj (tens A.t Λ).G

abbrev bPt : Over (Sp ↥(intO ↥C.S)) := (Over.pullback (spMap A.f)).obj (abTens A.U Λ)

abbrev gtLev (e : ℕ) : Over (Sp (↥(intO ↥C.S) ⧸ defIdeal A ^ (e + 1))) := thickObj _ (defIdeal A) e (gPt A Λ)

abbrev bLev (e : ℕ) : Over (Sp (↥(intO ↥C.S) ⧸ defIdeal A ^ (e + 1))) := thickObj _ (defIdeal A) e (bPt A Λ)

abbrev gtTrans (e : ℕ) : (gtLev A Λ e).left ⟶ (gtLev A Λ (e + 1)).left := thickMap _ (defIdeal A) e (gPt A Λ)

def levToDat (G : Over (Sp A.R)) (e : ℕ) : (thickObj _ (defIdeal A) e ((Over.pullback (spMap A.f)).obj G)).left ⟶
    (thickObj A.R (maximalIdeal A.R) e G).left := hMap (φ := A.f) (hφ := le_rfl) G _ (𝟙 _)

def prLev (e : ℕ) : gtLev A Λ e ⟶ bLev A Λ e :=
  Over.homMk ((isGrpPullback_levToDat A (abTens A.U Λ) e).1.lift (levToDat A _ e ≫ (qTens A.U Λ e).left) (gtLev A Λ e).hom
    (by rw [Category.assoc, Over.w]; exact (isGrpPullback_levToDat A _ e).1.w))
    ((isGrpPullback_levToDat A (abTens A.U Λ) e).1.lift_snd _ _ _)

def prPt (e : ℕ) : (gtLev A Λ e).left ⟶ (bPt A Λ).left := (prLev A Λ e).left ≫ pullback.fst _ _

abbrev GtPic : Type := FPic (X := fun e => (gtLev A Λ e).left) (gtTrans A Λ)

def prPullPt (M : SmallPic (bPt A Λ).left) : GtPic A Λ := fpull (prPt A Λ) (gtTrans_prPt A Λ) M

def completePt (L : SmallPic (gPt A Λ).left) : GtPic A Λ :=
  fpull (fun _ => pullback.fst _ _) (fun e => thickMap_fst _ e _) L

variable {X : Scheme.{0}} {π : X ⟶ Y.X} {t : SAB H X} (m : SABMap t Y.t π) (z : Sp ↥(intO ↥C.S) ⟶ X) (hz : z ≫ π = P.yt)

include hz in
theorem isGrpPullback_gPt_base : IsGrpPullback (gPt A Λ) (tens Y.t Λ).G (z ≫ π) (pullback.fst _ _ ≫ (tens.map Λ A.m).φ) :=
  ((isGrpPullback_pullback _ (spMap A.f)).comp (tens.map Λ A.m).cart).congr (A.fac.trans hz.symm) rfl

def gPtTo : (gPt A Λ).left ⟶ (tens t Λ).G.left :=
  (tens.map Λ m).cart.1.lift (pullback.fst _ _ ≫ (tens.map Λ A.m).φ) ((gPt A Λ).hom ≫ z)
    (by rw [(isGrpPullback_gPt_base A Λ z hz).1.w, Category.assoc])

end Point

section Generic

variable {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}
  {i₀ : Idx H p} (Z : Mdl Y i₀)

def Mdl.tQ : SAB H Z.genO.toScheme := (Geo.Tor.exists_sab Z.genO.ι Z.t).choose

def Mdl.tQMap : SABMap Z.tQ Z.t Z.genO.ι := (Geo.Tor.exists_sab Z.genO.ι Z.t).choose_spec.some

end Generic

section Record

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.ShFam

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

def thbTrue (ct : At S κ p) : ThbSt ct (uniTrue ct) where
  LBG Λ := SmallPic (tens ct.Xm.t Λ).G.left
  LBGq Λ := SmallPic (tens ct.Xm.tQ Λ).G.left
  resQ {Λ} := smallPull (tens.map Λ ct.Xm.tQMap).φ
  PPq Λ := tens.ppCls ct.Xm.tQ Λ
  symmG := IsSymCls _
  rigG := IsRigCls _
  LBGt y Λ := GtPic (ct.dat y) Λ
  LBB y Λ := SmallPic (bPt (ct.dat y) Λ).left
  resGt {Λ} L y := completePt (ct.dat y) Λ (smallPull (gPtTo (ct.dat y) Λ ct.Xm.tMap y.z y.z_π) L)
  prPull {y Λ} := prPullPt (ct.dat y) Λ
  principal := IsPrincipalCls _
  StrictHenselianAcyclic Λ := RigPic ((tens ct.Xm.t Λ).G ⊗ (tens ct.Xm.t Λ).G)
  squareRootLineBundle Λ := RigPic ((tens ct.Xm.tQ Λ).G ⊗ (tens ct.Xm.tQ Λ).G)
  res2 {Λ} := sqPull (tens.map Λ ct.Xm.tQMap).cart
  PoiQ Λ := tens.poiCls ct.Xm.tQ Λ
  biext := IsBiextCls
  dg {Λ} := tens.diag ct.Xm.t Λ
  dgq {Λ} := tens.diag ct.Xm.tQ Λ
  dg_res {Λ} P := tens.smallPull_diag Λ ct.Xm.tQMap P
  PPq_def Λ := (tens.diag_poiCls ct.Xm.tQ Λ).symm

variable (ct : At S κ p) (Λ : (uniTrue ct).Unim)

end Record

end GlobalTheory.LocM
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RestrictionPoincareBundle =====
