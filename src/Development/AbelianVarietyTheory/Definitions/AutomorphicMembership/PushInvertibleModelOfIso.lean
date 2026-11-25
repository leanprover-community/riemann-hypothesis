module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaSqMulSqrtEtaSq
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericPointMemModuliOfMeetsAbelianLocus
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyOfModToModIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperRestrictPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushforwardPolarisationBundleInvertibleOnModel
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open GlobalTheory.FlagMod (GChart thUnit thRat detChg pushPP detOm detLie de ev)
open GlobalTheory.Reg (MChart)
open GlobalTheory.LB (toMod)

namespace GlobalTheory.LocM

section OneModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

section Transport

variable (Y : Model Xo c β) {X : Scheme.{0}} (π : X ⟶ Y.X) [IsIso π]

def genInv : pullback Y.s (spMap β) ⟶ pullback (π ≫ Y.s) (spMap β) :=
  pullback.map _ _ _ _ (inv π) (𝟙 _) (𝟙 _) (by simp) (by simp)

instance isIso_genInv : IsIso (genInv Y π) := by unfold genInv; infer_instance

@[reducible] def modelOfIso (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (t : SAB H X) (m : SABMap t Y.t π) :
    Model Xo c β where
  X := X
  s := π ≫ Y.s
  normal := hn
  proj := by
    obtain ⟨n, i, hi, e⟩ := Y.proj
    exact ⟨n, π ≫ i, inferInstance, by rw [Category.assoc, e]⟩
  flat := have := Y.flat; inferInstance
  jQ := Y.jQ ≫ genInv Y π
  jQ_over := by rw [Category.assoc, genInv_snd, Y.jQ_over]
  jQ_open := have := Y.jQ_open; inferInstance
  jQ_dense := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp]
    exact (genInv Y π).surjective.denseRange.comp Y.jQ_dense (genInv Y π).continuous
  t := t
  oF := Y.oF
  m0 := Y.m0
  m := (exists_sabMap_genInv Y π m).choose
  ab_gen := by
    ext y
    obtain ⟨y, rfl⟩ := (genInv Y π).surjective y
    rw [Set.mem_preimage, ← abLocus_pullback abLocusOne Y.t.semi m.cart.1, ← Scheme.Hom.comp_apply,
      ← Scheme.Hom.comp_apply, genInv_fst, ← Set.mem_preimage, Y.ab_gen]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, Scheme.Hom.comp_apply _ _ _⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, (genInv Y π).homeomorph.injective ((Scheme.Hom.comp_apply _ _ _).symm.trans hx)⟩

end Transport

variable {Y : Model Xo c β}

def pushMod {X : Scheme.{0}} (t : SAB H X) : X.Modules := (Scheme.Modules.pushforward t.G.hom).obj (toMod t.PP.L)

def keyUnit (k : ℕ) (M M' : GChart Y) : Γ(Y.X, M.U ⊓ M'.U)ˣ :=
  (thUnit M M')⁻¹ ^ (2 * k) * detChg M.toMChart M'.toMChart ^ k

def keyLB (Y : Model Xo c β) (k : ℕ) : LB Y.X := ⟨GChart Y, fun M => M.U, keyUnit k⟩

def KeyAt (M : GChart Y) {R : Type} [CommRing R] (z : Sp R ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U) (x : KeyIn R) : Prop :=
  ∃ (φ : x.P.A.left ⟶ Y.t.G.left) (he : eSec x.P.A ≫ φ = z ≫ eSec Y.t.G)
    (w : LB.Iso x.P.L (Y.t.PP.L.pull φ)) (hg : x.P.g = M.n),
    IsGrpPullback x.P.A Y.t.G z φ ∧ w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec x.P.A) (fun _ => 1)) x.rig
      (rigPullOf φ z he Y.t.PP.L Y.t.PP.rig) ∧
    (∀ (j : (Y.t.PP.L.pull φ).ι) (i : x.P.L.ι)
      (h : (Y.t.PP.L.pull φ).U j ⊓ x.P.L.U i ≤ φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U (j PUnit.unit))),
      (φ.appLE _ _ h).hom (M.θ (j PUnit.unit)) =
        (show Γ(x.P.A.left, (Y.t.PP.L.pull φ).U j ⊓ x.P.L.U i) from (w.s (j, i)).val) *
          resG _ inf_le_right (x.th.f i)) ∧
    ∀ i, (x.v i).left ≫ φ = spMap (_root_.Formalism.L2.Pj.dualMap (ev z M.U hz)) ≫ M.v₀ (i.cast hg)

end OneModel

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

namespace At

variable (ct : At S κ p)

@[reducible] def base : Model (S.Xo ct.Xm.i.l) ct.Xm.i.c (ct.Xm.i.c.V ct.W).subtype :=
  haveI := ct.B.iso none
  modelOfIso (ct.Y ct.Xm.i) ct.Xm.π (@GlobalTheory.IsNormalScheme.pred _ ct.Xm.normal) ct.Xm.t ct.Xm.tMap

instance isNoetherianRing_base : IsNoetherianRing (ct.Xm.i.c.V ct.W) :=
  GlobalTheory.ModelPresentation.isNoetherianRing_place _ _ ct.hp.ne_zero ct.hW

abbrev KeyChart : Type := GChart ct.base

def keyL (c : ℕ) : LB ct.Xm.X := keyLB ct.base c

def ofModIso {Z : ct.Mdl} {F : Z.X.Modules} (h : GlobalTheory.VB.IsVB F 1) : (Z.ofMod F).toMod ≅ F :=
  haveI := h.isFiniteQC
  (GlobalTheory.ModelPresentation.nonempty_ofMod_toMod_iso _ _ _ _ p ct.W ct.hp ct.hW _ _ Z F).some

def piPP : ct.Sh ct.Xm := ct.Xm.ofMod (pushMod ct.Xm.t)

def keySh (c : ℕ) : ct.Sh ct.Xm := ct.Xm.ofMod (toMod (ct.keyL c))

def keyIso (c : ℕ) : (ct.keySh c).toMod ≅ toMod (ct.keyL c) := ct.ofModIso (GlobalTheory.VB.isVB_toMod (ct.isLB_keyL c))

variable {ct}

def keyGen (c : ℕ) (M : ct.KeyChart) : Γ((ct.keySh c).toMod, M.U) :=
  (ct.keyIso c).inv.app M.U (GlobalTheory.LB.chartSec (ct.isLB_keyL c) M)

def keyCoef {c : ℕ} {V : ct.Xm.X.Opens} (s : Γ((ct.keySh c).toMod, V)) (M : ct.KeyChart) : Γ(ct.Xm.X, V ⊓ M.U) :=
  GlobalTheory.LB.coord ((ct.keyIso c).hom.app V s) M

def keyMk (c : ℕ) {V : ct.Xm.X.Opens} (f : ∀ M : ct.KeyChart, Γ(ct.Xm.X, V ⊓ M.U)) (hf : f ∈ secOn (ct.keyL c) V) :
    Γ((ct.keySh c).toMod, V) :=
  (GlobalTheory.LB.appLinearEquiv (ct.keyIso c) V).symm (GlobalTheory.LB.mkSec f hf)

def HasKeyValues {c : ℕ} (val : GlobalTheory.KeyCl.Rule) (s : ct.Sec (ct.keySh c)) : Prop :=
  ∀ (M : ct.KeyChart) (K : Type) [Field K] [CharZero K] (z : Sp K ⟶ ct.Xm.X) (hz : ⊤ ≤ z ⁻¹ᵁ (ct.Xm.genO ⊓ M.U))
    (x : KeyIn K), KeyAt M z (GlobalTheory.FlagMod.le_preimage_mono inf_le_right hz) x → ev z _ hz (keyCoef s M) = val K x

variable (ct)

open Classical in
def pbKF {g c : ℕ} (kf : KF g c) : ct.Sec (ct.keySh c) :=
  if h : ∃ s : ct.Sec (ct.keySh c), HasKeyValues kf.coef s then h.choose else 0

end At

def keyTrue (ct : At S κ p) : KeySt ct where
  piPP := ct.piPP
  keySh := ct.keySh
  keySh_inv _ := ct.isInv_keySh

end GlobalTheory.LocM
